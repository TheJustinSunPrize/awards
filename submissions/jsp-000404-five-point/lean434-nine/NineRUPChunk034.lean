import Mathlib.Tactic.Tauto

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

namespace NineRUPTrial

theorem step42150 (p17 p185 p189 : Prop)
    (h42123 : (¬ p189))
    (h42130 : (¬ p185))
    (h42038 : (¬ p17) ∨ p189 ∨ p185) : (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p189) := by
    exact h42123
  have u2 : (¬ p185) := by
    exact h42130
  rcases h42038 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (u2 q2)

theorem step42151 (p189 p234 p790 : Prop)
    (h42123 : (¬ p189))
    (h42118 : p234)
    (h39870 : (¬ p234) ∨ p790 ∨ p189) : p790 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p790) := fun hu => hn hu
  have u1 : (¬ p189) := by
    exact h42123
  have u2 : p234 := by
    exact h42118
  rcases h39870 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)

theorem step42160 (p422 p1253 : Prop)
    (h42132 : p422)
    (h33808 : p1253 ∨ (¬ p422)) : p1253 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1253) := fun hu => hn hu
  have u1 : p422 := by
    exact h42132
  rcases h33808 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)

theorem step42161 (p422 p1252 : Prop)
    (h42132 : p422)
    (h34294 : p1252 ∨ (¬ p422)) : p1252 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1252) := fun hu => hn hu
  have u1 : p422 := by
    exact h42132
  rcases h34294 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)

theorem step42162 (p15 p422 p1229 : Prop)
    (h42132 : p422)
    (h42131 : (¬ p15))
    (h38609 : (¬ p422) ∨ p15 ∨ (¬ p1229)) : (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p422 := by
    exact h42132
  have u2 : (¬ p15) := by
    exact h42131
  rcases h38609 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u0)

theorem step42166 (p15 p24 p50 p134 p495 : Prop)
    (h42136 : p50)
    (h42131 : (¬ p15))
    (h42108 : p134)
    (h41977 : p24)
    (h27151 : p495 ∨ p15 ∨ (¬ p24) ∨ (¬ p50) ∨ (¬ p134)) : p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p495) := fun hu => hn hu
  have u1 : p50 := by
    exact h42136
  have u2 : (¬ p15) := by
    exact h42131
  have u3 : p134 := by
    exact h42108
  have u4 : p24 := by
    exact h41977
  rcases h27151 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)

theorem step42167 (p25 p50 p124 p134 p210 p633 : Prop)
    (h42136 : p50)
    (h41789 : p210)
    (h41978 : p25)
    (h42114 : (¬ p124))
    (h42108 : p134)
    (h32242 : (¬ p50) ∨ (¬ p210) ∨ (¬ p25) ∨ (¬ p633) ∨ p124 ∨ (¬ p134)) : (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p50 := by
    exact h42136
  have u2 : p210 := by
    exact h41789
  have u3 : p25 := by
    exact h41978
  have u4 : (¬ p124) := by
    exact h42114
  have u5 : p134 := by
    exact h42108
  rcases h32242 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u5)

theorem step42184 (p421 p495 : Prop)
    (h42166 : p495)
    (h27236 : p421 ∨ (¬ p495)) : p421 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p421) := fun hu => hn hu
  have u1 : p495 := by
    exact h42166
  rcases h27236 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)

theorem step42189 (p3 p134 p163 p224 p633 p1076 : Prop)
    (h42167 : (¬ p633))
    (h42064 : p224)
    (h42108 : p134)
    (h42115 : (¬ p163))
    (h41782 : p3)
    (h34816 : (¬ p3) ∨ p633 ∨ (¬ p1076) ∨ (¬ p134) ∨ p163 ∨ (¬ p224)) : (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p633) := by
    exact h42167
  have u2 : p224 := by
    exact h42064
  have u3 : p134 := by
    exact h42108
  have u4 : (¬ p163) := by
    exact h42115
  have u5 : p3 := by
    exact h41782
  rcases h34816 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u2)

theorem step42196 (p1076 p1084 : Prop)
    (h42189 : (¬ p1076))
    (h24284 : p1084 ∨ p1076) : p1084 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1084) := fun hu => hn hu
  have u1 : (¬ p1076) := by
    exact h42189
  rcases h24284 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)

theorem step42197 (p2 p8 p12 p50 p103 p106 p134 p163 p186 p224 p225 p285 p303 p308 p324 p344 p420 p424 p434 p435 p438 p455 p495 p532 p539 p560 p561 p662 p884 p897 p980 p1038 p1055 p1076 p1084 p1096 p1140 p1253 p1325 p1335 p1346 p1366 p1489 p1508 : Prop)
    (h42014 : p106)
    (h41784 : p561)
    (h41795 : p103)
    (h42136 : p50)
    (h41972 : p884)
    (h42065 : p662)
    (h42115 : (¬ p163))
    (h41785 : p560)
    (h42077 : p344)
    (h42196 : p1084)
    (h42081 : (¬ p2))
    (h42133 : (¬ p1096))
    (h42064 : p224)
    (h42144 : p186)
    (h42160 : p1253)
    (h41967 : p308)
    (h42108 : p134)
    (h41742 : p285)
    (h42189 : (¬ p1076))
    (h42166 : p495)
    (h42069 : p1335)
    (h33767 : p539 ∨ (¬ p225))
    (h34918 : (¬ p103) ∨ (¬ p344) ∨ p420 ∨ (¬ p225) ∨ (¬ p106))
    (h13475 : (¬ p12) ∨ (¬ p225) ∨ (¬ p662))
    (h36640 : (¬ p561) ∨ p163 ∨ (¬ p8) ∨ (¬ p225))
    (h12633 : (¬ p103) ∨ p324 ∨ (¬ p539))
    (h11507 : (¬ p103) ∨ (¬ p134) ∨ (¬ p424) ∨ (¬ p539))
    (h24904 : p1038 ∨ p12)
    (h38226 : p303 ∨ p8 ∨ (¬ p224) ∨ (¬ p308))
    (h33093 : p8 ∨ (¬ p884) ∨ p163 ∨ p897 ∨ (¬ p560) ∨ (¬ p50))
    (h32956 : p1055 ∨ p8 ∨ (¬ p662))
    (h31955 : p163 ∨ p8 ∨ (¬ p1325) ∨ (¬ p224) ∨ (¬ p560))
    (h30463 : p424 ∨ (¬ p1038) ∨ p2 ∨ p1140 ∨ p1076)
    (h33310 : (¬ p344) ∨ (¬ p1084) ∨ (¬ p455) ∨ (¬ p897))
    (h30484 : (¬ p1366) ∨ (¬ p224) ∨ (¬ p897) ∨ p1096 ∨ p2)
    (h32066 : p455 ∨ p1325 ∨ (¬ p532) ∨ (¬ p495))
    (h13840 : (¬ p186) ∨ (¬ p1140) ∨ (¬ p1253) ∨ p1346)
    (h21910 : p1366 ∨ p435)
    (h37482 : p532 ∨ (¬ p980) ∨ (¬ p1055) ∨ (¬ p308))
    (h18623 : (¬ p134) ∨ (¬ p303) ∨ (¬ p324) ∨ (¬ p434) ∨ (¬ p435))
    (h28015 : (¬ p1489) ∨ p980 ∨ p1076 ∨ (¬ p285))
    (h21060 : p438 ∨ p434)
    (h21548 : p1508 ∨ p1489)
    (h36922 : (¬ p438) ∨ (¬ p420) ∨ (¬ p1346) ∨ (¬ p1335) ∨ (¬ p1508) ∨ (¬ p495)) : (¬ p225) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p106 := by
    exact h42014
  have u2 : p561 := by
    exact h41784
  have u3 : p103 := by
    exact h41795
  have u4 : p50 := by
    exact h42136
  have u5 : p884 := by
    exact h41972
  have u6 : p662 := by
    exact h42065
  have u7 : (¬ p163) := by
    exact h42115
  have u8 : p560 := by
    exact h41785
  have u9 : p344 := by
    exact h42077
  have u10 : p1084 := by
    exact h42196
  have u11 : (¬ p2) := by
    exact h42081
  have u12 : (¬ p1096) := by
    exact h42133
  have u13 : p224 := by
    exact h42064
  have u14 : p186 := by
    exact h42144
  have u15 : p1253 := by
    exact h42160
  have u16 : p308 := by
    exact h41967
  have u17 : p134 := by
    exact h42108
  have u18 : p285 := by
    exact h41742
  have u19 : (¬ p1076) := by
    exact h42189
  have u20 : p495 := by
    exact h42166
  have u21 : p1335 := by
    exact h42069
  have u22 : p539 := by
    rcases h33767 with q0 | q1
    · exact q0
    · exact False.elim (q1 u0)
  have u23 : p420 := by
    rcases h34918 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u3)
    · exact False.elim (q1 u9)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u1)
  have u24 : (¬ p12) := by
    rcases h13475 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u6)
  have u25 : (¬ p8) := by
    rcases h36640 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u2)
    · exact False.elim (u7 q1)
    · exact q2
    · exact False.elim (q3 u0)
  have u26 : p324 := by
    rcases h12633 with q0 | q1 | q2
    · exact False.elim (q0 u3)
    · exact q1
    · exact False.elim (q2 u22)
  have u27 : (¬ p424) := by
    rcases h11507 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u3)
    · exact False.elim (q1 u17)
    · exact q2
    · exact False.elim (q3 u22)
  have u28 : p1038 := by
    rcases h24904 with q0 | q1
    · exact q0
    · exact False.elim (u24 q1)
  have u29 : p303 := by
    rcases h38226 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (u25 q1)
    · exact False.elim (q2 u13)
    · exact False.elim (q3 u16)
  have u30 : p897 := by
    rcases h33093 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (u25 q0)
    · exact False.elim (q1 u5)
    · exact False.elim (u7 q2)
    · exact q3
    · exact False.elim (q4 u8)
    · exact False.elim (q5 u4)
  have u31 : p1055 := by
    rcases h32956 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u25 q1)
    · exact False.elim (q2 u6)
  have u32 : (¬ p1325) := by
    rcases h31955 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (u7 q0)
    · exact False.elim (u25 q1)
    · exact q2
    · exact False.elim (q3 u13)
    · exact False.elim (q4 u8)
  have u33 : p1140 := by
    rcases h30463 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (u27 q0)
    · exact False.elim (q1 u28)
    · exact False.elim (u11 q2)
    · exact q3
    · exact False.elim (u19 q4)
  have u34 : (¬ p455) := by
    rcases h33310 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u9)
    · exact False.elim (q1 u10)
    · exact q2
    · exact False.elim (q3 u30)
  have u35 : (¬ p1366) := by
    rcases h30484 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u13)
    · exact False.elim (q2 u30)
    · exact False.elim (u12 q3)
    · exact False.elim (u11 q4)
  have u36 : (¬ p532) := by
    rcases h32066 with q0 | q1 | q2 | q3
    · exact False.elim (u34 q0)
    · exact False.elim (u32 q1)
    · exact q2
    · exact False.elim (q3 u20)
  have u37 : p1346 := by
    rcases h13840 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u14)
    · exact False.elim (q1 u33)
    · exact False.elim (q2 u15)
    · exact q3
  have u38 : p435 := by
    rcases h21910 with q0 | q1
    · exact False.elim (u35 q0)
    · exact q1
  have u39 : (¬ p980) := by
    rcases h37482 with q0 | q1 | q2 | q3
    · exact False.elim (u36 q0)
    · exact q1
    · exact False.elim (q2 u31)
    · exact False.elim (q3 u16)
  have u40 : (¬ p434) := by
    rcases h18623 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u17)
    · exact False.elim (q1 u29)
    · exact False.elim (q2 u26)
    · exact q3
    · exact False.elim (q4 u38)
  have u41 : (¬ p1489) := by
    rcases h28015 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (u39 q1)
    · exact False.elim (u19 q2)
    · exact False.elim (q3 u18)
  have u42 : p438 := by
    rcases h21060 with q0 | q1
    · exact q0
    · exact False.elim (u40 q1)
  have u43 : p1508 := by
    rcases h21548 with q0 | q1
    · exact q0
    · exact False.elim (u41 q1)
  rcases h36922 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u42)
  · exact False.elim (q1 u23)
  · exact False.elim (q2 u37)
  · exact False.elim (q3 u21)
  · exact False.elim (q4 u43)
  · exact False.elim (q5 u20)

theorem step42198 (p1 p225 : Prop)
    (h42197 : (¬ p225))
    (h21617 : p1 ∨ p225) : p1 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1) := fun hu => hn hu
  have u1 : (¬ p225) := by
    exact h42197
  rcases h21617 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)

theorem step42213 (p3 p6 p10 p12 p17 p124 p125 p126 p134 p345 p350 p367 p420 p421 p434 p438 p595 p600 p633 p687 p690 p980 p1076 p1287 p1335 p1542 p1545 : Prop)
    (h42108 : p134)
    (h42184 : p421)
    (h41787 : (¬ p6))
    (h42189 : (¬ p1076))
    (h42150 : (¬ p17))
    (h41782 : p3)
    (h42069 : p1335)
    (h42114 : (¬ p124))
    (h42167 : (¬ p633))
    (h21948 : p367 ∨ p125)
    (h31653 : p125 ∨ p124 ∨ (¬ p134) ∨ (¬ p10))
    (h27042 : p124 ∨ (¬ p345) ∨ p125)
    (h28309 : (¬ p420) ∨ (¬ p421) ∨ p125)
    (h38710 : p10 ∨ p6 ∨ p126)
    (h33981 : p12 ∨ p1076 ∨ p10)
    (h21667 : p350 ∨ p345)
    (h20956 : p600 ∨ p420)
    (h35967 : (¬ p126) ∨ (¬ p434) ∨ p17 ∨ (¬ p1287) ∨ p595)
    (h28433 : (¬ p12) ∨ (¬ p3) ∨ (¬ p1545) ∨ p595 ∨ p980 ∨ (¬ p1335))
    (h21060 : p438 ∨ p434)
    (h20851 : p1542 ∨ p1545)
    (h28380 : p124 ∨ (¬ p687) ∨ (¬ p350) ∨ (¬ p438))
    (h30156 : (¬ p1542) ∨ (¬ p690) ∨ (¬ p367) ∨ (¬ p600) ∨ p633 ∨ (¬ p350))
    (h20766 : p690 ∨ p687) : p125 ∨ p980 ∨ (¬ p1287) ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p125) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p134 := by
    exact h42108
  have u5 : p421 := by
    exact h42184
  have u6 : (¬ p6) := by
    exact h41787
  have u7 : (¬ p1076) := by
    exact h42189
  have u8 : (¬ p17) := by
    exact h42150
  have u9 : p3 := by
    exact h41782
  have u10 : p1335 := by
    exact h42069
  have u11 : (¬ p124) := by
    exact h42114
  have u12 : (¬ p633) := by
    exact h42167
  have u13 : p367 := by
    rcases h21948 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u14 : (¬ p10) := by
    rcases h31653 with q0 | q1 | q2 | q3
    · exact False.elim (u0 q0)
    · exact False.elim (u11 q1)
    · exact False.elim (q2 u4)
    · exact q3
  have u15 : (¬ p345) := by
    rcases h27042 with q0 | q1 | q2
    · exact False.elim (u11 q0)
    · exact q1
    · exact False.elim (u0 q2)
  have u16 : (¬ p420) := by
    rcases h28309 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u5)
    · exact False.elim (u0 q2)
  have u17 : p126 := by
    rcases h38710 with q0 | q1 | q2
    · exact False.elim (u14 q0)
    · exact False.elim (u6 q1)
    · exact q2
  have u18 : p12 := by
    rcases h33981 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u7 q1)
    · exact False.elim (u14 q2)
  have u19 : p350 := by
    rcases h21667 with q0 | q1
    · exact q0
    · exact False.elim (u15 q1)
  have u20 : p600 := by
    rcases h20956 with q0 | q1
    · exact q0
    · exact False.elim (u16 q1)
  have u21 : (¬ p434) := by
    rcases h35967 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u17)
    · exact q1
    · exact False.elim (u8 q2)
    · exact False.elim (q3 u2)
    · exact False.elim (u3 q4)
  have u22 : (¬ p1545) := by
    rcases h28433 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u18)
    · exact False.elim (q1 u9)
    · exact q2
    · exact False.elim (u3 q3)
    · exact False.elim (u1 q4)
    · exact False.elim (q5 u10)
  have u23 : p438 := by
    rcases h21060 with q0 | q1
    · exact q0
    · exact False.elim (u21 q1)
  have u24 : p1542 := by
    rcases h20851 with q0 | q1
    · exact q0
    · exact False.elim (u22 q1)
  have u25 : (¬ p687) := by
    rcases h28380 with q0 | q1 | q2 | q3
    · exact False.elim (u11 q0)
    · exact q1
    · exact False.elim (q2 u19)
    · exact False.elim (q3 u23)
  have u26 : (¬ p690) := by
    rcases h30156 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u24)
    · exact q1
    · exact False.elim (q2 u13)
    · exact False.elim (q3 u20)
    · exact False.elim (u12 q4)
    · exact False.elim (q5 u19)
  rcases h20766 with q0 | q1
  · exact False.elim (u26 q0)
  · exact False.elim (u25 q1)

theorem step42214 (p1 p2 p3 p6 p10 p12 p50 p125 p134 p163 p186 p210 p225 p234 p303 p324 p382 p420 p424 p434 p435 p438 p480 p495 p595 p614 p633 p663 p728 p734 p980 p1035 p1038 p1076 p1140 p1286 p1287 p1335 p1366 p1465 : Prop)
    (h41787 : (¬ p6))
    (h42082 : p480)
    (h42118 : p234)
    (h42144 : p186)
    (h42136 : p50)
    (h42167 : (¬ p633))
    (h41789 : p210)
    (h42115 : (¬ p163))
    (h41782 : p3)
    (h42067 : p663)
    (h42197 : (¬ p225))
    (h42189 : (¬ p1076))
    (h42081 : (¬ p2))
    (h42166 : p495)
    (h42069 : p1335)
    (h42198 : p1)
    (h42108 : p134)
    (h40953 : p382 ∨ (¬ p303))
    (h21715 : p614 ∨ p595)
    (h41104 : (¬ p1286) ∨ (¬ p50) ∨ (¬ p614) ∨ (¬ p134) ∨ (¬ p382) ∨ (¬ p186) ∨ (¬ p234) ∨ (¬ p480) ∨ p6)
    (h20657 : p1287 ∨ p1286)
    (h40727 : p980 ∨ (¬ p1465) ∨ p225)
    (h21566 : p1465 ∨ p1035)
    (h42213 : p125 ∨ p980 ∨ (¬ p1287) ∨ p595)
    (h27275 : (¬ p125) ∨ (¬ p210) ∨ p10)
    (h30175 : (¬ p210) ∨ (¬ p125) ∨ (¬ p134) ∨ p633 ∨ p420)
    (h34149 : p324 ∨ (¬ p10))
    (h26098 : (¬ p420) ∨ (¬ p495) ∨ (¬ p12) ∨ (¬ p3) ∨ (¬ p303))
    (h36546 : p163 ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p424) ∨ (¬ p3))
    (h24904 : p1038 ∨ p12)
    (h33033 : p225 ∨ (¬ p728) ∨ (¬ p663) ∨ p12)
    (h30463 : p424 ∨ (¬ p1038) ∨ p2 ∨ p1140 ∨ p1076)
    (h20753 : p728 ∨ p734)
    (h26088 : (¬ p495) ∨ (¬ p420) ∨ (¬ p438) ∨ (¬ p1035) ∨ (¬ p1335) ∨ (¬ p1140))
    (h35940 : (¬ p734) ∨ (¬ p1366) ∨ (¬ p1) ∨ p12)
    (h21060 : p438 ∨ p434)
    (h21910 : p1366 ∨ p435)
    (h18623 : (¬ p134) ∨ (¬ p303) ∨ (¬ p324) ∨ (¬ p434) ∨ (¬ p435)) : p980 ∨ p595 ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p595) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p6) := by
    exact h41787
  have u4 : p480 := by
    exact h42082
  have u5 : p234 := by
    exact h42118
  have u6 : p186 := by
    exact h42144
  have u7 : p50 := by
    exact h42136
  have u8 : (¬ p633) := by
    exact h42167
  have u9 : p210 := by
    exact h41789
  have u10 : (¬ p163) := by
    exact h42115
  have u11 : p3 := by
    exact h41782
  have u12 : p663 := by
    exact h42067
  have u13 : (¬ p225) := by
    exact h42197
  have u14 : (¬ p1076) := by
    exact h42189
  have u15 : (¬ p2) := by
    exact h42081
  have u16 : p495 := by
    exact h42166
  have u17 : p1335 := by
    exact h42069
  have u18 : p1 := by
    exact h42198
  have u19 : p134 := by
    exact h42108
  have u20 : p382 := by
    rcases h40953 with q0 | q1
    · exact q0
    · exact False.elim (q1 u2)
  have u21 : p614 := by
    rcases h21715 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u22 : (¬ p1286) := by
    rcases h41104 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
    · exact q0
    · exact False.elim (q1 u7)
    · exact False.elim (q2 u21)
    · exact False.elim (q3 u19)
    · exact False.elim (q4 u20)
    · exact False.elim (q5 u6)
    · exact False.elim (q6 u5)
    · exact False.elim (q7 u4)
    · exact False.elim (u3 q8)
  have u23 : p1287 := by
    rcases h20657 with q0 | q1
    · exact q0
    · exact False.elim (u22 q1)
  have u24 : (¬ p1465) := by
    rcases h40727 with q0 | q1 | q2
    · exact False.elim (u0 q0)
    · exact q1
    · exact False.elim (u13 q2)
  have u25 : p1035 := by
    rcases h21566 with q0 | q1
    · exact False.elim (u24 q0)
    · exact q1
  have u26 : p125 := by
    rcases h42213 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u23)
    · exact False.elim (u1 q3)
  have u27 : p10 := by
    rcases h27275 with q0 | q1 | q2
    · exact False.elim (q0 u26)
    · exact False.elim (q1 u9)
    · exact q2
  have u28 : p420 := by
    rcases h30175 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u9)
    · exact False.elim (q1 u26)
    · exact False.elim (q2 u19)
    · exact False.elim (u8 q3)
    · exact q4
  have u29 : p324 := by
    rcases h34149 with q0 | q1
    · exact q0
    · exact False.elim (q1 u27)
  have u30 : (¬ p12) := by
    rcases h26098 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u28)
    · exact False.elim (q1 u16)
    · exact q2
    · exact False.elim (q3 u11)
    · exact False.elim (q4 u2)
  have u31 : (¬ p424) := by
    rcases h36546 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (u10 q0)
    · exact False.elim (q1 u28)
    · exact False.elim (q2 u16)
    · exact q3
    · exact False.elim (q4 u11)
  have u32 : p1038 := by
    rcases h24904 with q0 | q1
    · exact q0
    · exact False.elim (u30 q1)
  have u33 : (¬ p728) := by
    rcases h33033 with q0 | q1 | q2 | q3
    · exact False.elim (u13 q0)
    · exact q1
    · exact False.elim (q2 u12)
    · exact False.elim (u30 q3)
  have u34 : p1140 := by
    rcases h30463 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (u31 q0)
    · exact False.elim (q1 u32)
    · exact False.elim (u15 q2)
    · exact q3
    · exact False.elim (u14 q4)
  have u35 : p734 := by
    rcases h20753 with q0 | q1
    · exact False.elim (u33 q0)
    · exact q1
  have u36 : (¬ p438) := by
    rcases h26088 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u16)
    · exact False.elim (q1 u28)
    · exact q2
    · exact False.elim (q3 u25)
    · exact False.elim (q4 u17)
    · exact False.elim (q5 u34)
  have u37 : (¬ p1366) := by
    rcases h35940 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u35)
    · exact q1
    · exact False.elim (q2 u18)
    · exact False.elim (u30 q3)
  have u38 : p434 := by
    rcases h21060 with q0 | q1
    · exact False.elim (u36 q0)
    · exact q1
  have u39 : p435 := by
    rcases h21910 with q0 | q1
    · exact False.elim (u37 q0)
    · exact q1
  rcases h18623 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u19)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u29)
  · exact False.elim (q3 u38)
  · exact False.elim (q4 u39)

theorem step42215 (p3 p6 p12 p14 p50 p134 p161 p185 p186 p225 p234 p303 p382 p422 p423 p480 p595 p614 p665 p980 p1035 p1042 p1115 p1122 p1140 p1146 p1229 p1252 p1286 p1287 p1325 p1465 p1489 p1508 : Prop)
    (h42108 : p134)
    (h42144 : p186)
    (h42118 : p234)
    (h42082 : p480)
    (h41787 : (¬ p6))
    (h42197 : (¬ p225))
    (h42066 : p665)
    (h42162 : (¬ p1229))
    (h41782 : p3)
    (h41969 : p14)
    (h42130 : (¬ p185))
    (h42132 : p422)
    (h42136 : p50)
    (h42161 : p1252)
    (h40953 : p382 ∨ (¬ p303))
    (h21715 : p614 ∨ p595)
    (h41104 : (¬ p1286) ∨ (¬ p50) ∨ (¬ p614) ∨ (¬ p134) ∨ (¬ p382) ∨ (¬ p186) ∨ (¬ p234) ∨ (¬ p480) ∨ p6)
    (h20657 : p1287 ∨ p1286)
    (h42214 : p980 ∨ p595 ∨ (¬ p303))
    (h28948 : p225 ∨ p1325 ∨ p12 ∨ (¬ p980))
    (h33811 : p1042 ∨ (¬ p12))
    (h37253 : (¬ p1115) ∨ (¬ p12) ∨ (¬ p3))
    (h27982 : p1325 ∨ (¬ p161) ∨ p1229 ∨ (¬ p3) ∨ (¬ p12) ∨ (¬ p665))
    (h13487 : (¬ p3) ∨ (¬ p1042) ∨ p1140)
    (h12201 : (¬ p14) ∨ p423 ∨ (¬ p1042))
    (h25352 : p1122 ∨ p1115)
    (h33667 : p1146 ∨ (¬ p423))
    (h39673 : (¬ p980) ∨ (¬ p1508) ∨ p185 ∨ p595 ∨ (¬ p1287) ∨ (¬ p1122))
    (h29640 : (¬ p422) ∨ p161 ∨ (¬ p1146) ∨ (¬ p50) ∨ (¬ p1465))
    (h21548 : p1508 ∨ p1489)
    (h21566 : p1465 ∨ p1035)
    (h36146 : (¬ p1489) ∨ (¬ p1252) ∨ (¬ p1140) ∨ (¬ p1035)) : p595 ∨ p1325 ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p595) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p134 := by
    exact h42108
  have u4 : p186 := by
    exact h42144
  have u5 : p234 := by
    exact h42118
  have u6 : p480 := by
    exact h42082
  have u7 : (¬ p6) := by
    exact h41787
  have u8 : (¬ p225) := by
    exact h42197
  have u9 : p665 := by
    exact h42066
  have u10 : (¬ p1229) := by
    exact h42162
  have u11 : p3 := by
    exact h41782
  have u12 : p14 := by
    exact h41969
  have u13 : (¬ p185) := by
    exact h42130
  have u14 : p422 := by
    exact h42132
  have u15 : p50 := by
    exact h42136
  have u16 : p1252 := by
    exact h42161
  have u17 : p382 := by
    rcases h40953 with q0 | q1
    · exact q0
    · exact False.elim (q1 u2)
  have u18 : p614 := by
    rcases h21715 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u19 : (¬ p1286) := by
    rcases h41104 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
    · exact q0
    · exact False.elim (q1 u15)
    · exact False.elim (q2 u18)
    · exact False.elim (q3 u3)
    · exact False.elim (q4 u17)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u5)
    · exact False.elim (q7 u6)
    · exact False.elim (u7 q8)
  have u20 : p1287 := by
    rcases h20657 with q0 | q1
    · exact q0
    · exact False.elim (u19 q1)
  have u21 : p980 := by
    rcases h42214 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u2)
  have u22 : p12 := by
    rcases h28948 with q0 | q1 | q2 | q3
    · exact False.elim (u8 q0)
    · exact False.elim (u1 q1)
    · exact q2
    · exact False.elim (q3 u21)
  have u23 : p1042 := by
    rcases h33811 with q0 | q1
    · exact q0
    · exact False.elim (q1 u22)
  have u24 : (¬ p1115) := by
    rcases h37253 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u22)
    · exact False.elim (q2 u11)
  have u25 : (¬ p161) := by
    rcases h27982 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (u1 q0)
    · exact q1
    · exact False.elim (u10 q2)
    · exact False.elim (q3 u11)
    · exact False.elim (q4 u22)
    · exact False.elim (q5 u9)
  have u26 : p1140 := by
    rcases h13487 with q0 | q1 | q2
    · exact False.elim (q0 u11)
    · exact False.elim (q1 u23)
    · exact q2
  have u27 : p423 := by
    rcases h12201 with q0 | q1 | q2
    · exact False.elim (q0 u12)
    · exact q1
    · exact False.elim (q2 u23)
  have u28 : p1122 := by
    rcases h25352 with q0 | q1
    · exact q0
    · exact False.elim (u24 q1)
  have u29 : p1146 := by
    rcases h33667 with q0 | q1
    · exact q0
    · exact False.elim (q1 u27)
  have u30 : (¬ p1508) := by
    rcases h39673 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u21)
    · exact q1
    · exact False.elim (u13 q2)
    · exact False.elim (u0 q3)
    · exact False.elim (q4 u20)
    · exact False.elim (q5 u28)
  have u31 : (¬ p1465) := by
    rcases h29640 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u14)
    · exact False.elim (u25 q1)
    · exact False.elim (q2 u29)
    · exact False.elim (q3 u15)
    · exact q4
  have u32 : p1489 := by
    rcases h21548 with q0 | q1
    · exact False.elim (u30 q0)
    · exact q1
  have u33 : p1035 := by
    rcases h21566 with q0 | q1
    · exact False.elim (u31 q0)
    · exact q1
  rcases h36146 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u32)
  · exact False.elim (q1 u16)
  · exact False.elim (q2 u26)
  · exact False.elim (q3 u33)

theorem step42216 (p3 p15 p24 p163 p420 p424 p495 p595 p596 p633 : Prop)
    (h42131 : (¬ p15))
    (h42167 : (¬ p633))
    (h41977 : p24)
    (h42115 : (¬ p163))
    (h42166 : p495)
    (h41782 : p3)
    (h40728 : p15 ∨ (¬ p595) ∨ p424)
    (h39302 : p633 ∨ (¬ p596) ∨ (¬ p24) ∨ (¬ p595) ∨ (¬ p495))
    (h36546 : p163 ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p424) ∨ (¬ p3))
    (h22572 : p596 ∨ p420) : (¬ p595) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p15) := by
    exact h42131
  have u2 : (¬ p633) := by
    exact h42167
  have u3 : p24 := by
    exact h41977
  have u4 : (¬ p163) := by
    exact h42115
  have u5 : p495 := by
    exact h42166
  have u6 : p3 := by
    exact h41782
  have u7 : p424 := by
    rcases h40728 with q0 | q1 | q2
    · exact False.elim (u1 q0)
    · exact False.elim (q1 u0)
    · exact q2
  have u8 : (¬ p596) := by
    rcases h39302 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (u2 q0)
    · exact q1
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u5)
  have u9 : (¬ p420) := by
    rcases h36546 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (u4 q0)
    · exact q1
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u7)
    · exact False.elim (q4 u6)
  rcases h22572 with q0 | q1
  · exact False.elim (u8 q0)
  · exact False.elim (u9 q1)

theorem step42217 (p595 p614 : Prop)
    (h42216 : (¬ p595))
    (h21715 : p614 ∨ p595) : p614 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p614) := fun hu => hn hu
  have u1 : (¬ p595) := by
    exact h42216
  rcases h21715 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)

theorem step42219 (p6 p10 p50 p124 p125 p134 p185 p186 p210 p234 p303 p348 p382 p480 p495 p595 p614 p633 p1286 p1287 p1325 : Prop)
    (h42136 : p50)
    (h42144 : p186)
    (h42118 : p234)
    (h42082 : p480)
    (h41787 : (¬ p6))
    (h42217 : p614)
    (h42108 : p134)
    (h41789 : p210)
    (h42216 : (¬ p595))
    (h42079 : p348)
    (h42114 : (¬ p124))
    (h42167 : (¬ p633))
    (h42166 : p495)
    (h42130 : (¬ p185))
    (h40953 : p382 ∨ (¬ p303))
    (h42215 : p595 ∨ p1325 ∨ (¬ p303))
    (h41104 : (¬ p1286) ∨ (¬ p50) ∨ (¬ p614) ∨ (¬ p134) ∨ (¬ p382) ∨ (¬ p186) ∨ (¬ p234) ∨ (¬ p480) ∨ p6)
    (h16996 : (¬ p10) ∨ (¬ p134) ∨ (¬ p303) ∨ (¬ p1325))
    (h20657 : p1287 ∨ p1286)
    (h27275 : (¬ p125) ∨ (¬ p210) ∨ p10)
    (h37255 : p633 ∨ p595 ∨ p124 ∨ (¬ p495) ∨ (¬ p1325) ∨ (¬ p1287) ∨ (¬ p348) ∨ p185 ∨ p125) : (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p50 := by
    exact h42136
  have u2 : p186 := by
    exact h42144
  have u3 : p234 := by
    exact h42118
  have u4 : p480 := by
    exact h42082
  have u5 : (¬ p6) := by
    exact h41787
  have u6 : p614 := by
    exact h42217
  have u7 : p134 := by
    exact h42108
  have u8 : p210 := by
    exact h41789
  have u9 : (¬ p595) := by
    exact h42216
  have u10 : p348 := by
    exact h42079
  have u11 : (¬ p124) := by
    exact h42114
  have u12 : (¬ p633) := by
    exact h42167
  have u13 : p495 := by
    exact h42166
  have u14 : (¬ p185) := by
    exact h42130
  have u15 : p382 := by
    rcases h40953 with q0 | q1
    · exact q0
    · exact False.elim (q1 u0)
  have u16 : p1325 := by
    rcases h42215 with q0 | q1 | q2
    · exact False.elim (u9 q0)
    · exact q1
    · exact False.elim (q2 u0)
  have u17 : (¬ p1286) := by
    rcases h41104 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
    · exact q0
    · exact False.elim (q1 u1)
    · exact False.elim (q2 u6)
    · exact False.elim (q3 u7)
    · exact False.elim (q4 u15)
    · exact False.elim (q5 u2)
    · exact False.elim (q6 u3)
    · exact False.elim (q7 u4)
    · exact False.elim (u5 q8)
  have u18 : (¬ p10) := by
    rcases h16996 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u7)
    · exact False.elim (q2 u0)
    · exact False.elim (q3 u16)
  have u19 : p1287 := by
    rcases h20657 with q0 | q1
    · exact q0
    · exact False.elim (u17 q1)
  have u20 : (¬ p125) := by
    rcases h27275 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u8)
    · exact False.elim (u18 q2)
  rcases h37255 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u12 q0)
  · exact False.elim (u9 q1)
  · exact False.elim (u11 q2)
  · exact False.elim (q3 u13)
  · exact False.elim (q4 u16)
  · exact False.elim (q5 u19)
  · exact False.elim (q6 u10)
  · exact False.elim (u14 q7)
  · exact False.elim (u20 q8)

theorem step42220 (p3 p225 p303 p351 p595 p1287 : Prop)
    (h42216 : (¬ p595))
    (h42080 : p351)
    (h42219 : (¬ p303))
    (h41782 : p3)
    (h42197 : (¬ p225))
    (h28434 : p303 ∨ (¬ p3) ∨ p225 ∨ (¬ p1287) ∨ p595 ∨ (¬ p351)) : (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p595) := by
    exact h42216
  have u2 : p351 := by
    exact h42080
  have u3 : (¬ p303) := by
    exact h42219
  have u4 : p3 := by
    exact h41782
  have u5 : (¬ p225) := by
    exact h42197
  rcases h28434 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u0)
  · exact False.elim (u1 q4)
  · exact False.elim (q5 u2)

theorem step42228 (p224 p303 p420 p633 : Prop)
    (h42219 : (¬ p303))
    (h42167 : (¬ p633))
    (h42064 : p224)
    (h27561 : p303 ∨ p633 ∨ (¬ p224) ∨ p420) : p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p420) := fun hu => hn hu
  have u1 : (¬ p303) := by
    exact h42219
  have u2 : (¬ p633) := by
    exact h42167
  have u3 : p224 := by
    exact h42064
  rcases h27561 with q0 | q1 | q2 | q3
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (u0 q3)

theorem step42230 (p1286 p1287 : Prop)
    (h42220 : (¬ p1287))
    (h20657 : p1287 ∨ p1286) : p1286 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1286) := fun hu => hn hu
  have u1 : (¬ p1287) := by
    exact h42220
  rcases h20657 with q0 | q1
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)

theorem step42243 (p224 p351 p420 p495 p789 p790 : Prop)
    (h42228 : p420)
    (h42166 : p495)
    (h42080 : p351)
    (h42151 : p790)
    (h42064 : p224)
    (h36969 : (¬ p790) ∨ (¬ p420) ∨ (¬ p224) ∨ (¬ p351) ∨ (¬ p495) ∨ (¬ p789)) : (¬ p789) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p420 := by
    exact h42228
  have u2 : p495 := by
    exact h42166
  have u3 : p351 := by
    exact h42080
  have u4 : p790 := by
    exact h42151
  have u5 : p224 := by
    exact h42064
  rcases h36969 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u0)

theorem step42244 (p3 p163 p420 p424 p495 : Prop)
    (h42228 : p420)
    (h41782 : p3)
    (h42166 : p495)
    (h42115 : (¬ p163))
    (h36546 : p163 ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p424) ∨ (¬ p3)) : (¬ p424) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p420 := by
    exact h42228
  have u2 : p3 := by
    exact h41782
  have u3 : p495 := by
    exact h42166
  have u4 : (¬ p163) := by
    exact h42115
  rcases h36546 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u2)

theorem step42250 (p6 p50 p134 p186 p234 p382 p480 p614 p1286 : Prop)
    (h42230 : p1286)
    (h41787 : (¬ p6))
    (h42082 : p480)
    (h42118 : p234)
    (h42144 : p186)
    (h42217 : p614)
    (h42108 : p134)
    (h42136 : p50)
    (h41104 : (¬ p1286) ∨ (¬ p50) ∨ (¬ p614) ∨ (¬ p134) ∨ (¬ p382) ∨ (¬ p186) ∨ (¬ p234) ∨ (¬ p480) ∨ p6) : (¬ p382) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p1286 := by
    exact h42230
  have u2 : (¬ p6) := by
    exact h41787
  have u3 : p480 := by
    exact h42082
  have u4 : p234 := by
    exact h42118
  have u5 : p186 := by
    exact h42144
  have u6 : p614 := by
    exact h42217
  have u7 : p134 := by
    exact h42108
  have u8 : p50 := by
    exact h42136
  rcases h41104 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u3)
  · exact False.elim (u2 q8)

theorem step42264 (p2 p382 p424 p789 : Prop)
    (h42243 : (¬ p789))
    (h42244 : (¬ p424))
    (h42081 : (¬ p2))
    (h42250 : (¬ p382))
    (h37388 : p424 ∨ p2 ∨ p382 ∨ p789) : False := by
  classical
  have u0 : (¬ p789) := by
    exact h42243
  have u1 : (¬ p424) := by
    exact h42244
  have u2 : (¬ p2) := by
    exact h42081
  have u3 : (¬ p382) := by
    exact h42250
  rcases h37388 with q0 | q1 | q2 | q3
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (u3 q2)
  · exact False.elim (u0 q3)

#print axioms step42264

end NineRUPTrial
