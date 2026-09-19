import Mathlib.Tactic.Tauto

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

namespace NineRUPTrial

theorem step28735 (p17 p256 p455 p633 p636 p1349 p1493 : Prop)
    (h26885 : p636 ∨ p633)
    (h26853 : p256 ∨ p17)
    (h18785 : (¬ p256) ∨ (¬ p455) ∨ (¬ p636) ∨ (¬ p1349) ∨ (¬ p1493)) : (¬ p1493) ∨ (¬ p455) ∨ (¬ p1349) ∨ p633 ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1493 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p633) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18785 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u0)

theorem step28736 (p41 p45 p124 p189 p193 p420 p521 p601 p633 p636 p862 p1349 : Prop)
    (h26845 : p193 ∨ p189)
    (h26885 : p636 ∨ p633)
    (h26831 : p45 ∨ p41)
    (h26881 : p601 ∨ p420)
    (h19849 : (¬ p45) ∨ (¬ p124) ∨ (¬ p193) ∨ (¬ p521) ∨ (¬ p601) ∨ (¬ p636) ∨ (¬ p862) ∨ (¬ p1349)) : (¬ p1349) ∨ p189 ∨ (¬ p862) ∨ (¬ p124) ∨ (¬ p521) ∨ p633 ∨ p41 ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p862 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p521 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p633) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h19849 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u0)

theorem step28738 (p41 p45 p163 p167 p1273 p1349 : Prop)
    (h26831 : p45 ∨ p41)
    (h26843 : p167 ∨ p163)
    (h16846 : (¬ p45) ∨ (¬ p167) ∨ (¬ p1273) ∨ (¬ p1349)) : p41 ∨ (¬ p1273) ∨ (¬ p1349) ∨ p163 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p41) := fun hu => hn (Or.inl hu)
  have u1 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16846 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)

theorem step28739 (p185 p237 p576 p581 p918 p1349 : Prop)
    (h26851 : p237 ∨ p185)
    (h26879 : p581 ∨ p576)
    (h18353 : (¬ p237) ∨ (¬ p581) ∨ (¬ p918) ∨ (¬ p1349)) : (¬ p1349) ∨ p185 ∨ p576 ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18353 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)

theorem step28740 (p303 p387 p517 p790 p857 p1349 : Prop)
    (h26867 : p387 ∨ p303)
    (h18692 : (¬ p387) ∨ (¬ p517) ∨ (¬ p790) ∨ (¬ p857) ∨ (¬ p1349)) : p303 ∨ (¬ p1349) ∨ (¬ p790) ∨ (¬ p857) ∨ (¬ p517) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p857 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p517 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h18692 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)

theorem step28741 (p14 p189 p193 p229 p423 p1253 p1349 : Prop)
    (h26849 : p229 ∨ p14)
    (h26845 : p193 ∨ p189)
    (h18712 : (¬ p193) ∨ (¬ p229) ∨ (¬ p423) ∨ (¬ p1253) ∨ (¬ p1349)) : p14 ∨ (¬ p1253) ∨ (¬ p1349) ∨ p189 ∨ (¬ p423) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : p1253 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18712 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)

theorem step28742 (p185 p237 p917 p1095 p1118 p1349 : Prop)
    (h26851 : p237 ∨ p185)
    (h16319 : (¬ p237) ∨ (¬ p917) ∨ (¬ p1095) ∨ (¬ p1118) ∨ (¬ p1349)) : (¬ p1349) ∨ (¬ p917) ∨ p185 ∨ (¬ p1118) ∨ (¬ p1095) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p917 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1118 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16319 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u0)

theorem step28743 (p17 p256 p576 p1076 p1077 p1118 p1349 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26853 : p256 ∨ p17)
    (h17739 : (¬ p256) ∨ (¬ p576) ∨ (¬ p1077) ∨ (¬ p1118) ∨ (¬ p1349)) : (¬ p1118) ∨ (¬ p576) ∨ (¬ p1349) ∨ p1076 ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1118 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17739 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u2)

theorem step28744 (p90 p160 p1249 p1353 p1489 : Prop)
    (h26586 : p90)
    (h16727 : (¬ p90) ∨ (¬ p160) ∨ (¬ p1249) ∨ (¬ p1353) ∨ (¬ p1489)) : (¬ p160) ∨ (¬ p1353) ∨ (¬ p1489) ∨ (¬ p1249) := by
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
  have u2 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p90 := by
    exact h26586
  rcases h16727 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)

theorem step28745 (p404 p1226 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h11322 : (¬ p404) ∨ (¬ p1226) ∨ (¬ p1333)) : (¬ p404) ∨ p1325 ∨ (¬ p1226) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p404 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h11322 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)

theorem step28746 (p308 p980 p983 p1056 p1076 p1077 p1226 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26903 : p983 ∨ p980)
    (h16802 : (¬ p308) ∨ (¬ p983) ∨ (¬ p1056) ∨ (¬ p1077) ∨ (¬ p1226)) : p1076 ∨ p980 ∨ (¬ p1226) ∨ (¬ p1056) ∨ (¬ p308) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1076) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1056 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p308 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16802 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)

theorem step28747 (p125 p126 p301 p362 p959 p1035 p1226 : Prop)
    (h26857 : p301 ∨ p126)
    (h26865 : p362 ∨ p125)
    (h18365 : (¬ p301) ∨ (¬ p362) ∨ (¬ p959) ∨ (¬ p1035) ∨ (¬ p1226)) : (¬ p959) ∨ (¬ p1226) ∨ (¬ p1035) ∨ p126 ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p959 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p126) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18365 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u1)

theorem step28748 (p124 p258 p959 p980 p983 p1226 : Prop)
    (h26903 : p983 ∨ p980)
    (h18849 : (¬ p124) ∨ (¬ p258) ∨ (¬ p959) ∨ (¬ p983) ∨ (¬ p1226)) : (¬ p959) ∨ p980 ∨ (¬ p124) ∨ (¬ p1226) ∨ (¬ p258) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p959 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18849 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)

theorem step28750 (p11 p264 p532 p1226 p1443 : Prop)
    (h26935 : p1443 ∨ p11)
    (h25606 : (¬ p1226) ∨ p532 ∨ (¬ p264) ∨ (¬ p1443)) : p532 ∨ (¬ p1226) ∨ (¬ p264) ∨ p11 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p532) := fun hu => hn (Or.inl hu)
  have u1 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p264 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h25606 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step28751 (p11 p48 p68 p88 p124 p211 p228 p258 p1226 p1325 p1333 p1354 p1443 : Prop)
    (h26935 : p1443 ∨ p11)
    (h26931 : p1333 ∨ p1325)
    (h18771 : (¬ p48) ∨ (¬ p68) ∨ (¬ p88) ∨ (¬ p124) ∨ (¬ p211) ∨ (¬ p228) ∨ (¬ p258) ∨ (¬ p1226) ∨ (¬ p1333) ∨ (¬ p1354) ∨ (¬ p1443)) : (¬ p258) ∨ (¬ p211) ∨ (¬ p1354) ∨ (¬ p124) ∨ (¬ p1226) ∨ (¬ p48) ∨ (¬ p68) ∨ p11 ∨ (¬ p88) ∨ p1325 ∨ (¬ p228) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1354 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u12 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h18771 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u12)
  · exact False.elim (q9 u2)
  · exact False.elim (q10 u11)

theorem step28753 (p15 p63 p85 p423 p1000 p1226 p1235 p1274 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26835 : p85 ∨ p63)
    (h16550 : (¬ p15) ∨ (¬ p85) ∨ (¬ p423) ∨ (¬ p1000) ∨ (¬ p1226) ∨ (¬ p1235) ∨ (¬ p1274) ∨ (¬ p1333)) : p1325 ∨ (¬ p1226) ∨ (¬ p15) ∨ (¬ p1235) ∨ (¬ p1000) ∨ p63 ∨ (¬ p1274) ∨ (¬ p423) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1325) := fun hu => hn (Or.inl hu)
  have u1 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1235 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1274 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h16550 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u8)

theorem step28754 (p303 p387 p599 p1226 p1235 p1288 p1325 p1333 : Prop)
    (h26867 : p387 ∨ p303)
    (h26931 : p1333 ∨ p1325)
    (h16574 : (¬ p387) ∨ (¬ p599) ∨ (¬ p1226) ∨ (¬ p1235) ∨ (¬ p1288) ∨ (¬ p1333)) : p303 ∨ p1325 ∨ (¬ p599) ∨ (¬ p1235) ∨ (¬ p1288) ∨ (¬ p1226) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p599 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1235 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16574 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u7)

theorem step28755 (p18 p185 p210 p237 p918 p959 p1226 p1273 p1452 p1490 : Prop)
    (h26851 : p237 ∨ p185)
    (h20626 : (¬ p18) ∨ (¬ p210) ∨ (¬ p237) ∨ (¬ p918) ∨ (¬ p959) ∨ (¬ p1226) ∨ (¬ p1273) ∨ (¬ p1452) ∨ (¬ p1490)) : (¬ p1452) ∨ (¬ p1226) ∨ p185 ∨ (¬ p959) ∨ (¬ p1273) ∨ (¬ p210) ∨ (¬ p1490) ∨ (¬ p18) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p959 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1490 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20626 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u0)
  · exact False.elim (q8 u6)

theorem step28756 (p836 p840 p1060 p1115 p1226 p1452 : Prop)
    (h26895 : p840 ∨ p836)
    (h18924 : (¬ p840) ∨ (¬ p1060) ∨ (¬ p1115) ∨ (¬ p1226) ∨ (¬ p1452)) : (¬ p1115) ∨ (¬ p1226) ∨ (¬ p1452) ∨ (¬ p1060) ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1060 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18924 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)

theorem step28758 (p576 p581 p980 p983 p1226 p1249 p1352 : Prop)
    (h26903 : p983 ∨ p980)
    (h26879 : p581 ∨ p576)
    (h17429 : (¬ p581) ∨ (¬ p983) ∨ (¬ p1226) ∨ (¬ p1249) ∨ (¬ p1352)) : p980 ∨ (¬ p1226) ∨ (¬ p1249) ∨ p576 ∨ (¬ p1352) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1352 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17429 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u4)

theorem step28759 (p126 p264 p303 p363 p382 p387 : Prop)
    (h26867 : p387 ∨ p303)
    (h16866 : (¬ p126) ∨ (¬ p264) ∨ (¬ p363) ∨ (¬ p382) ∨ (¬ p387)) : p303 ∨ (¬ p382) ∨ (¬ p126) ∨ (¬ p363) ∨ (¬ p264) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p363 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p264 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h16866 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)

theorem step28760 (p125 p264 p518 p576 p1385 p1393 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h19817 : (¬ p125) ∨ (¬ p264) ∨ (¬ p518) ∨ (¬ p576) ∨ (¬ p1393)) : (¬ p576) ∨ p1385 ∨ (¬ p264) ∨ (¬ p125) ∨ (¬ p518) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1385) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p264 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p518 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19817 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)

theorem step28761 (p124 p264 p287 p304 p344 p346 p836 p840 : Prop)
    (h26859 : p304 ∨ p124)
    (h26895 : p840 ∨ p836)
    (h26863 : p346 ∨ p344)
    (h16863 : (¬ p264) ∨ (¬ p287) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p840)) : p124 ∨ (¬ p287) ∨ p836 ∨ (¬ p264) ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p264 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16863 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u6)

theorem step28762 (p124 p264 p287 p304 p1076 p1115 p1116 : Prop)
    (h26859 : p304 ∨ p124)
    (h26915 : p1116 ∨ p1115)
    (h19004 : (¬ p264) ∨ (¬ p287) ∨ (¬ p304) ∨ (¬ p1076) ∨ (¬ p1116)) : p124 ∨ (¬ p287) ∨ (¬ p264) ∨ (¬ p1076) ∨ p1115 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p264 := by
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
  rcases h19004 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)

theorem step28764 (p734 p789 p858 p897 p1022 : Prop)
    (h26897 : p858 ∨ p789)
    (h17872 : (¬ p734) ∨ (¬ p858) ∨ (¬ p897) ∨ (¬ p1022)) : (¬ p1022) ∨ (¬ p897) ∨ (¬ p734) ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17872 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)

theorem step28765 (p101 p102 p258 p519 p734 p1022 : Prop)
    (h26837 : p102 ∨ p101)
    (h18514 : (¬ p102) ∨ (¬ p258) ∨ (¬ p519) ∨ (¬ p734) ∨ (¬ p1022)) : (¬ p1022) ∨ (¬ p258) ∨ (¬ p519) ∨ (¬ p734) ∨ p101 := by
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
  have u2 : p519 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18514 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u0)

theorem step28776 (p424 p796 p803 p804 p805 p806 p807 p808 : Prop)
    (h26890 : (¬ p424) ∨ (¬ p796))
    (h4557 : p796 ∨ p803 ∨ (¬ p804) ∨ (¬ p805) ∨ (¬ p806) ∨ (¬ p807) ∨ (¬ p808)) : p803 ∨ (¬ p807) ∨ (¬ p424) ∨ (¬ p804) ∨ (¬ p806) ∨ (¬ p805) ∨ (¬ p808) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p803) := fun hu => hn (Or.inl hu)
  have u1 : p807 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p804 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p806 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p805 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p808 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p796) := by
    rcases h26890 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h4557 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u7 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u6)

theorem step28777 (p2 p84 p186 p438 p481 p595 p603 p616 p929 p1096 p1366 : Prop)
    (h26873 : p481 ∨ p2)
    (h26883 : p616 ∨ p595)
    (h16975 : (¬ p84) ∨ (¬ p186) ∨ (¬ p438) ∨ (¬ p481) ∨ (¬ p603) ∨ (¬ p616) ∨ (¬ p929) ∨ (¬ p1096) ∨ (¬ p1366)) : (¬ p1366) ∨ (¬ p438) ∨ (¬ p84) ∨ p2 ∨ (¬ p186) ∨ (¬ p603) ∨ (¬ p1096) ∨ p595 ∨ (¬ p929) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p603 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h16975 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u0)

theorem step28778 (p2 p186 p303 p419 p434 p481 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h26873 : p481 ∨ p2)
    (h16978 : (¬ p186) ∨ (¬ p303) ∨ (¬ p434) ∨ (¬ p481) ∨ (¬ p996)) : (¬ p434) ∨ p419 ∨ (¬ p303) ∨ (¬ p186) ∨ p2 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p419) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16978 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step28779 (p2 p186 p224 p481 p657 p734 p1366 : Prop)
    (h26887 : p657 ∨ p224)
    (h26873 : p481 ∨ p2)
    (h17015 : (¬ p186) ∨ (¬ p481) ∨ (¬ p657) ∨ (¬ p734) ∨ (¬ p1366)) : (¬ p734) ∨ (¬ p1366) ∨ p224 ∨ p2 ∨ (¬ p186) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17015 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)

theorem step28781 (p90 p186 p382 p406 p475 p789 p858 p1385 : Prop)
    (h26869 : p406 ∨ p382)
    (h26586 : p90)
    (h26897 : p858 ∨ p789)
    (h17761 : (¬ p90) ∨ (¬ p186) ∨ (¬ p406) ∨ (¬ p475) ∨ (¬ p858) ∨ (¬ p1385)) : p382 ∨ (¬ p1385) ∨ (¬ p186) ∨ p789 ∨ (¬ p475) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p475 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p90 := by
    exact h26586
  have u7 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17761 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u1)

theorem step28782 (p2 p84 p186 p422 p424 p481 p495 p499 p582 p796 p1148 p1229 p1232 p1256 : Prop)
    (h26891 : p796 ∨ p424)
    (h26875 : p499 ∨ p495)
    (h26929 : p1256 ∨ p422)
    (h26873 : p481 ∨ p2)
    (h26927 : p1232 ∨ p1229)
    (h20269 : (¬ p84) ∨ (¬ p186) ∨ (¬ p481) ∨ (¬ p499) ∨ (¬ p582) ∨ (¬ p796) ∨ (¬ p1148) ∨ (¬ p1232) ∨ (¬ p1256)) : (¬ p1148) ∨ p424 ∨ p495 ∨ (¬ p84) ∨ p422 ∨ p2 ∨ (¬ p582) ∨ (¬ p186) ∨ p1229 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1148 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p424) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u12 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u13 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h20269 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u12)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u13)
  · exact False.elim (q8 u11)

theorem step28784 (p2 p84 p106 p163 p186 p424 p481 p756 p796 p929 p1538 : Prop)
    (h26891 : p796 ∨ p424)
    (h26873 : p481 ∨ p2)
    (h20281 : (¬ p84) ∨ (¬ p106) ∨ (¬ p163) ∨ (¬ p186) ∨ (¬ p481) ∨ (¬ p756) ∨ (¬ p796) ∨ (¬ p929) ∨ (¬ p1538)) : (¬ p1538) ∨ p424 ∨ (¬ p929) ∨ (¬ p106) ∨ p2 ∨ (¬ p186) ∨ (¬ p756) ∨ (¬ p163) ∨ (¬ p84) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1538 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p424) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20281 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u2)
  · exact False.elim (q8 u0)

theorem step28785 (p2 p17 p138 p186 p424 p481 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h26873 : p481 ∨ p2)
    (h16963 : (¬ p17) ∨ (¬ p138) ∨ (¬ p186) ∨ (¬ p481) ∨ (¬ p796)) : (¬ p186) ∨ p424 ∨ (¬ p138) ∨ p2 ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p424) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16963 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step28786 (p2 p156 p185 p186 p424 p481 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h26873 : p481 ∨ p2)
    (h16908 : (¬ p156) ∨ (¬ p185) ∨ (¬ p186) ∨ (¬ p481) ∨ (¬ p796)) : (¬ p156) ∨ p424 ∨ (¬ p186) ∨ p2 ∨ (¬ p185) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p424) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16908 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step28787 (p41 p45 p90 p186 p422 p1140 : Prop)
    (h26831 : p45 ∨ p41)
    (h26586 : p90)
    (h17243 : (¬ p45) ∨ (¬ p90) ∨ (¬ p186) ∨ (¬ p422) ∨ (¬ p1140)) : (¬ p186) ∨ (¬ p422) ∨ (¬ p1140) ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u5 : p90 := by
    exact h26586
  rcases h17243 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)

theorem step28788 (p2 p41 p45 p90 p186 p424 p481 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h26831 : p45 ∨ p41)
    (h26873 : p481 ∨ p2)
    (h26586 : p90)
    (h17423 : (¬ p45) ∨ (¬ p90) ∨ (¬ p186) ∨ (¬ p481) ∨ (¬ p796)) : (¬ p186) ∨ p424 ∨ p41 ∨ p2 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p424) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p90 := by
    exact h26586
  rcases h17423 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u4)

theorem step28789 (p2 p12 p163 p186 p424 p481 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h26873 : p481 ∨ p2)
    (h16826 : (¬ p12) ∨ (¬ p163) ∨ (¬ p186) ∨ (¬ p481) ∨ (¬ p796)) : p424 ∨ (¬ p163) ∨ (¬ p12) ∨ p2 ∨ (¬ p186) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16826 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step28790 (p3 p163 p167 p186 p422 p1210 p1226 p1256 p1354 p1452 : Prop)
    (h26843 : p167 ∨ p163)
    (h26929 : p1256 ∨ p422)
    (h16830 : (¬ p3) ∨ (¬ p167) ∨ (¬ p186) ∨ (¬ p1210) ∨ (¬ p1226) ∨ (¬ p1256) ∨ (¬ p1354) ∨ (¬ p1452)) : (¬ p1452) ∨ (¬ p1210) ∨ (¬ p1354) ∨ p163 ∨ p422 ∨ (¬ p1226) ∨ (¬ p186) ∨ (¬ p3) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1354 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16830 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u0)

theorem step28791 (p3 p163 p167 p186 p267 p303 p327 p363 p382 p387 p424 : Prop)
    (h26867 : p387 ∨ p303)
    (h26843 : p167 ∨ p163)
    (h17285 : (¬ p3) ∨ (¬ p167) ∨ (¬ p186) ∨ (¬ p267) ∨ (¬ p327) ∨ (¬ p363) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p424)) : (¬ p363) ∨ p303 ∨ p163 ∨ (¬ p267) ∨ (¬ p327) ∨ (¬ p3) ∨ (¬ p186) ∨ (¬ p382) ∨ (¬ p424) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p363 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p267 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p327 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17285 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u8)

theorem step28792 (p3 p163 p167 p186 p327 p424 p434 p690 p821 : Prop)
    (h26843 : p167 ∨ p163)
    (h17288 : (¬ p3) ∨ (¬ p167) ∨ (¬ p186) ∨ (¬ p327) ∨ (¬ p424) ∨ (¬ p434) ∨ (¬ p690) ∨ (¬ p821)) : (¬ p434) ∨ (¬ p690) ∨ (¬ p3) ∨ p163 ∨ (¬ p186) ∨ (¬ p327) ∨ (¬ p821) ∨ (¬ p424) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p327 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p821 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17288 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u6)

theorem step28793 (p3 p84 p163 p167 p186 p424 p495 p499 p582 p595 p616 p1287 : Prop)
    (h26875 : p499 ∨ p495)
    (h26843 : p167 ∨ p163)
    (h26883 : p616 ∨ p595)
    (h17297 : (¬ p3) ∨ (¬ p84) ∨ (¬ p167) ∨ (¬ p186) ∨ (¬ p424) ∨ (¬ p499) ∨ (¬ p582) ∨ (¬ p616) ∨ (¬ p1287)) : (¬ p186) ∨ (¬ p84) ∨ (¬ p3) ∨ p495 ∨ p163 ∨ p595 ∨ (¬ p424) ∨ (¬ p1287) ∨ (¬ p582) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1287 := by
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
    · exact False.elim (u3 q1)
  have u10 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17297 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u11)
  · exact False.elim (q8 u7)

theorem step28794 (p3 p125 p163 p167 p186 p267 p303 p424 p1325 : Prop)
    (h26843 : p167 ∨ p163)
    (h17284 : (¬ p3) ∨ (¬ p125) ∨ (¬ p167) ∨ (¬ p186) ∨ (¬ p267) ∨ (¬ p303) ∨ (¬ p424) ∨ (¬ p1325)) : (¬ p125) ∨ (¬ p3) ∨ p163 ∨ (¬ p186) ∨ (¬ p303) ∨ (¬ p267) ∨ (¬ p424) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p267 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17284 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u7)

theorem step28795 (p3 p41 p45 p90 p163 p167 p186 : Prop)
    (h26831 : p45 ∨ p41)
    (h26586 : p90)
    (h26843 : p167 ∨ p163)
    (h17705 : (¬ p3) ∨ (¬ p45) ∨ (¬ p90) ∨ (¬ p167) ∨ (¬ p186)) : p41 ∨ (¬ p3) ∨ (¬ p186) ∨ p163 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p41) := fun hu => hn (Or.inl hu)
  have u1 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p90 := by
    exact h26586
  have u6 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17705 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u2)

theorem step28797 (p255 p262 p576 p581 p757 p918 p1631 : Prop)
    (h26879 : p581 ∨ p576)
    (h20154 : (¬ p255) ∨ (¬ p262) ∨ (¬ p581) ∨ (¬ p757) ∨ (¬ p918) ∨ (¬ p1631)) : (¬ p757) ∨ (¬ p255) ∨ (¬ p918) ∨ (¬ p1631) ∨ p576 ∨ (¬ p262) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p757 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p255 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1631 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20154 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step28798 (p3 p105 p211 p226 p1631 p1666 : Prop)
    (h26847 : p226 ∨ p3)
    (h20164 : (¬ p105) ∨ (¬ p211) ∨ (¬ p226) ∨ (¬ p1631) ∨ (¬ p1666)) : (¬ p1631) ∨ (¬ p1666) ∨ (¬ p105) ∨ (¬ p211) ∨ p3 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1631 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1666 := by
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
  have u4 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20164 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)

theorem step28799 (p63 p85 p498 p582 p1604 p1631 : Prop)
    (h26835 : p85 ∨ p63)
    (h20153 : (¬ p85) ∨ (¬ p498) ∨ (¬ p582) ∨ (¬ p1604) ∨ (¬ p1631)) : (¬ p1604) ∨ (¬ p1631) ∨ (¬ p498) ∨ p63 ∨ (¬ p582) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1604 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1631 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20153 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)

theorem step28807 (p11 p455 p579 p1443 : Prop)
    (h26935 : p1443 ∨ p11)
    (h13230 : p455 ∨ (¬ p579) ∨ (¬ p1443)) : p455 ∨ (¬ p579) ∨ p11 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : p579 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p11) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h13230 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)

theorem step28808 (p386 p420 p455 p601 : Prop)
    (h26881 : p601 ∨ p420)
    (h14784 : (¬ p386) ∨ p455 ∨ (¬ p601)) : p455 ∨ (¬ p386) ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : p386 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h14784 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)

theorem step28810 (p11 p17 p86 p224 p228 p256 p897 p1096 p1099 p1443 : Prop)
    (h26935 : p1443 ∨ p11)
    (h26853 : p256 ∨ p17)
    (h26913 : p1099 ∨ p1096)
    (h18850 : (¬ p86) ∨ (¬ p224) ∨ (¬ p228) ∨ (¬ p256) ∨ (¬ p897) ∨ (¬ p1099) ∨ (¬ p1443)) : p11 ∨ p17 ∨ (¬ p228) ∨ (¬ p86) ∨ p1096 ∨ (¬ p897) ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p11) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18850 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u7)

theorem step28811 (p22 p124 p227 p228 p234 p304 p419 p633 p1187 : Prop)
    (h26859 : p304 ∨ p124)
    (h26921 : p1187 ∨ p234)
    (h18523 : (¬ p22) ∨ (¬ p227) ∨ (¬ p228) ∨ (¬ p304) ∨ (¬ p419) ∨ (¬ p633) ∨ (¬ p1187)) : (¬ p227) ∨ p124 ∨ (¬ p419) ∨ p234 ∨ (¬ p22) ∨ (¬ p633) ∨ (¬ p228) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p234) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p22 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18523 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u8)

theorem step28813 (p2 p18 p19 p67 p207 p227 p228 p997 p1325 p1333 p1465 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26829 : p19 ∨ p18)
    (h17333 : (¬ p2) ∨ (¬ p19) ∨ (¬ p67) ∨ (¬ p207) ∨ (¬ p227) ∨ (¬ p228) ∨ (¬ p997) ∨ (¬ p1333) ∨ (¬ p1465)) : (¬ p2) ∨ p1325 ∨ p18 ∨ (¬ p228) ∨ (¬ p207) ∨ (¬ p1465) ∨ (¬ p997) ∨ (¬ p227) ∨ (¬ p67) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p997 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17333 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u5)

theorem step28814 (p72 p228 p234 p382 p480 p532 p1035 p1140 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h19321 : (¬ p72) ∨ (¬ p228) ∨ (¬ p382) ∨ (¬ p480) ∨ (¬ p532) ∨ (¬ p1035) ∨ (¬ p1140) ∨ (¬ p1187)) : p234 ∨ (¬ p1035) ∨ (¬ p382) ∨ (¬ p532) ∨ (¬ p1140) ∨ (¬ p72) ∨ (¬ p228) ∨ (¬ p480) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p480 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19321 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u8)

theorem step28815 (p39 p68 p88 p101 p121 p124 p211 p228 p789 p790 p814 p858 : Prop)
    (h26897 : p858 ∨ p789)
    (h26893 : p814 ∨ p790)
    (h19610 : (¬ p39) ∨ (¬ p68) ∨ (¬ p88) ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p124) ∨ (¬ p211) ∨ (¬ p228) ∨ (¬ p814) ∨ (¬ p858)) : (¬ p101) ∨ (¬ p124) ∨ (¬ p228) ∨ (¬ p211) ∨ (¬ p39) ∨ p789 ∨ (¬ p68) ∨ (¬ p121) ∨ p790 ∨ (¬ p88) := by
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
  have u2 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u11 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h19610 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u2)
  · exact False.elim (q8 u11)
  · exact False.elim (q9 u10)

theorem step28816 (p303 p387 p596 p1287 : Prop)
    (h26867 : p387 ∨ p303)
    (h10839 : (¬ p387) ∨ (¬ p596) ∨ (¬ p1287)) : p303 ∨ (¬ p596) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p596 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h10839 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)

theorem step28817 (p303 p387 p596 p1286 : Prop)
    (h26867 : p387 ∨ p303)
    (h12971 : (¬ p387) ∨ (¬ p596) ∨ p1286) : p303 ∨ (¬ p596) ∨ p1286 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p596 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1286) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h12971 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (u2 q2)

theorem step28818 (p350 p495 p595 p596 p633 p636 : Prop)
    (h26885 : p636 ∨ p633)
    (h19255 : (¬ p350) ∨ (¬ p495) ∨ (¬ p595) ∨ (¬ p596) ∨ (¬ p636)) : p633 ∨ (¬ p350) ∨ (¬ p595) ∨ (¬ p495) ∨ (¬ p596) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p596 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19255 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)

theorem step28841 (p161 p163 p167 p422 p1164 p1225 p1235 p1256 p1325 : Prop)
    (h26925 : p1225 ∨ p161)
    (h26843 : p167 ∨ p163)
    (h26929 : p1256 ∨ p422)
    (h19551 : (¬ p167) ∨ (¬ p1164) ∨ (¬ p1225) ∨ (¬ p1235) ∨ (¬ p1256) ∨ (¬ p1325)) : p161 ∨ (¬ p1164) ∨ (¬ p1235) ∨ p163 ∨ (¬ p1325) ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p161) := fun hu => hn (Or.inl hu)
  have u1 : p1164 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1235 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19551 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u4)

theorem step28842 (p11 p84 p124 p258 p266 p1035 p1214 p1226 p1235 p1274 p1443 : Prop)
    (h26935 : p1443 ∨ p11)
    (h19504 : (¬ p84) ∨ (¬ p124) ∨ (¬ p258) ∨ (¬ p266) ∨ (¬ p1035) ∨ (¬ p1214) ∨ (¬ p1226) ∨ (¬ p1235) ∨ (¬ p1274) ∨ (¬ p1443)) : (¬ p1035) ∨ (¬ p1235) ∨ (¬ p84) ∨ (¬ p1274) ∨ (¬ p124) ∨ (¬ p258) ∨ (¬ p266) ∨ p11 ∨ (¬ p1214) ∨ (¬ p1226) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1235 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1274 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1214 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h19504 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u3)
  · exact False.elim (q9 u10)

theorem step28843 (p189 p193 p1250 p1346 : Prop)
    (h26845 : p193 ∨ p189)
    (h13825 : (¬ p193) ∨ (¬ p1250) ∨ p1346) : (¬ p1250) ∨ p1346 ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1250 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1346) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h13825 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (u1 q2)

theorem step28844 (p185 p237 p1122 p1346 : Prop)
    (h26851 : p237 ∨ p185)
    (h12098 : (¬ p237) ∨ (¬ p1122) ∨ p1346) : p1346 ∨ (¬ p1122) ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1346) := fun hu => hn (Or.inl hu)
  have u1 : p1122 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h12098 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (u0 q2)

theorem step28845 (p576 p581 p1273 p1492 : Prop)
    (h26878 : (¬ p576) ∨ (¬ p581))
    (h13781 : p581 ∨ (¬ p1273) ∨ (¬ p1492)) : (¬ p1492) ∨ (¬ p1273) ∨ (¬ p576) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1492 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p581) := by
    rcases h26878 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h13781 with q0 | q1 | q2
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)

theorem step28847 (p121 p258 p288 p1452 p1489 p1492 : Prop)
    (h26855 : p288 ∨ p258)
    (h18206 : (¬ p121) ∨ (¬ p288) ∨ (¬ p1452) ∨ (¬ p1489) ∨ (¬ p1492)) : (¬ p1452) ∨ (¬ p1489) ∨ (¬ p1492) ∨ p258 ∨ (¬ p121) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1492 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18206 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)

theorem step28848 (p303 p387 p518 p789 p858 : Prop)
    (h26867 : p387 ∨ p303)
    (h26897 : p858 ∨ p789)
    (h10679 : (¬ p387) ∨ (¬ p518) ∨ (¬ p858)) : p303 ∨ p789 ∨ (¬ p518) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p789) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p518 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h10679 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)

theorem step28849 (p63 p420 p518 p633 p1385 p1393 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h18578 : (¬ p63) ∨ (¬ p420) ∨ (¬ p518) ∨ (¬ p633) ∨ (¬ p1393)) : (¬ p420) ∨ p1385 ∨ (¬ p63) ∨ (¬ p633) ∨ (¬ p518) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1385) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p518 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18578 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)

theorem step28850 (p41 p45 p1015 p1392 p1542 : Prop)
    (h26831 : p45 ∨ p41)
    (h25869 : (¬ p1542) ∨ (¬ p1015) ∨ (¬ p1392) ∨ (¬ p45)) : (¬ p1542) ∨ (¬ p1392) ∨ p41 ∨ (¬ p1015) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1392 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h25869 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)

theorem step28853 (p14 p39 p63 p225 p303 p351 p382 p387 p544 p614 : Prop)
    (h26877 : p544 ∨ p225)
    (h26867 : p387 ∨ p303)
    (h19146 : (¬ p14) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p351) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p544) ∨ (¬ p614)) : p225 ∨ (¬ p614) ∨ (¬ p63) ∨ (¬ p39) ∨ (¬ p351) ∨ (¬ p382) ∨ p303 ∨ (¬ p14) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p225) := fun hu => hn (Or.inl hu)
  have u1 : p614 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19146 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u1)

theorem step28854 (p17 p185 p237 p283 : Prop)
    (h26851 : p237 ∨ p185)
    (h8758 : (¬ p17) ∨ (¬ p237) ∨ (¬ p283)) : (¬ p283) ∨ p185 ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p283 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h8758 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)

theorem step28855 (p126 p283 p350 p1076 p1077 p1115 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h18772 : (¬ p126) ∨ (¬ p283) ∨ (¬ p350) ∨ (¬ p1077) ∨ (¬ p1115)) : (¬ p1115) ∨ p1076 ∨ (¬ p350) ∨ (¬ p283) ∨ (¬ p126) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p283 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18772 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)

theorem step28857 (p124 p304 p310 : Prop)
    (h26858 : (¬ p124) ∨ (¬ p304))
    (h21128 : p310 ∨ p304) : p310 ∨ (¬ p124) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p310) := fun hu => hn (Or.inl hu)
  have u1 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p304) := by
    rcases h26858 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h21128 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step28858 (p124 p125 p304 p536 p726 : Prop)
    (h26858 : (¬ p124) ∨ (¬ p304))
    (h24185 : (¬ p536) ∨ (¬ p726) ∨ p304 ∨ (¬ p125)) : (¬ p125) ∨ (¬ p536) ∨ (¬ p726) ∨ (¬ p124) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
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
  have u3 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p304) := by
    rcases h26858 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h24185 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (u4 q2)
  · exact False.elim (q3 u0)

theorem step28859 (p124 p125 p349 p362 : Prop)
    (h26864 : (¬ p125) ∨ (¬ p362))
    (h7032 : (¬ p124) ∨ (¬ p349) ∨ p362) : (¬ p125) ∨ (¬ p349) ∨ (¬ p124) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p362) := by
    rcases h26864 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h7032 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (u3 q2)

theorem step28860 (p126 p258 p288 p349 : Prop)
    (h26855 : p288 ∨ p258)
    (h11985 : p126 ∨ (¬ p288) ∨ (¬ p349)) : p126 ∨ (¬ p349) ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h11985 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)

theorem step28861 (p124 p125 p304 p349 : Prop)
    (h26858 : (¬ p124) ∨ (¬ p304))
    (h11645 : (¬ p125) ∨ p304 ∨ (¬ p349)) : (¬ p125) ∨ (¬ p349) ∨ (¬ p124) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p304) := by
    rcases h26858 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h11645 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u1)

theorem step28864 (p17 p185 p256 p756 p1584 : Prop)
    (h26853 : p256 ∨ p17)
    (h17252 : (¬ p185) ∨ (¬ p256) ∨ (¬ p756) ∨ (¬ p1584)) : (¬ p756) ∨ (¬ p1584) ∨ (¬ p185) ∨ p17 := by
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
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17252 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)

theorem step28865 (p4 p126 p258 p288 p301 p738 p756 : Prop)
    (h26857 : p301 ∨ p126)
    (h26855 : p288 ∨ p258)
    (h17764 : (¬ p4) ∨ (¬ p288) ∨ (¬ p301) ∨ (¬ p738) ∨ (¬ p756)) : (¬ p756) ∨ p126 ∨ (¬ p4) ∨ p258 ∨ (¬ p738) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p738 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17764 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u0)

theorem step28867 (p3 p226 p756 p940 p1076 : Prop)
    (h26847 : p226 ∨ p3)
    (h17233 : (¬ p226) ∨ (¬ p756) ∨ (¬ p940) ∨ (¬ p1076)) : (¬ p756) ∨ (¬ p1076) ∨ p3 ∨ (¬ p940) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17233 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)

theorem step28869 (p537 p738 p835 p918 p928 p1385 : Prop)
    (h26901 : p928 ∨ p918)
    (h20212 : (¬ p537) ∨ (¬ p738) ∨ (¬ p835) ∨ (¬ p928) ∨ (¬ p1385)) : (¬ p537) ∨ (¬ p738) ∨ p918 ∨ (¬ p1385) ∨ (¬ p835) := by
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
  have u2 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p835 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20212 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)

theorem step28870 (p595 p616 p738 p899 p1096 p1562 : Prop)
    (h26883 : p616 ∨ p595)
    (h16470 : (¬ p616) ∨ (¬ p738) ∨ (¬ p899) ∨ (¬ p1096) ∨ (¬ p1562)) : (¬ p1096) ∨ (¬ p738) ∨ (¬ p899) ∨ (¬ p1562) ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p738 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p899 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1562 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16470 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u3)

theorem step28871 (p185 p237 p537 p738 p790 p814 p835 : Prop)
    (h26893 : p814 ∨ p790)
    (h26851 : p237 ∨ p185)
    (h20341 : (¬ p237) ∨ (¬ p537) ∨ (¬ p738) ∨ (¬ p814) ∨ (¬ p835)) : (¬ p537) ∨ p790 ∨ (¬ p835) ∨ (¬ p738) ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p790) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p835 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p738 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20341 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)

theorem step28872 (p17 p86 p256 p258 p288 p738 p756 p897 p1096 p1099 : Prop)
    (h26855 : p288 ∨ p258)
    (h26853 : p256 ∨ p17)
    (h26913 : p1099 ∨ p1096)
    (h17037 : (¬ p86) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p738) ∨ (¬ p756) ∨ (¬ p897) ∨ (¬ p1099)) : (¬ p756) ∨ (¬ p738) ∨ p258 ∨ p17 ∨ (¬ p86) ∨ p1096 ∨ (¬ p897) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p738 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17037 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u9)

theorem step28873 (p4 p10 p101 p102 p738 p756 : Prop)
    (h26837 : p102 ∨ p101)
    (h17999 : (¬ p4) ∨ (¬ p10) ∨ (¬ p102) ∨ (¬ p738) ∨ (¬ p756)) : (¬ p756) ∨ (¬ p10) ∨ (¬ p738) ∨ p101 ∨ (¬ p4) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p738 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17999 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u0)

theorem step28874 (p5 p6 p101 p344 p346 p738 p1096 p1562 : Prop)
    (h26863 : p346 ∨ p344)
    (h20003 : (¬ p5) ∨ (¬ p6) ∨ (¬ p101) ∨ (¬ p346) ∨ (¬ p738) ∨ (¬ p1096) ∨ (¬ p1562)) : (¬ p1562) ∨ (¬ p101) ∨ (¬ p6) ∨ (¬ p738) ∨ (¬ p1096) ∨ p344 ∨ (¬ p5) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1562 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p738 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20003 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u0)

theorem step28875 (p4 p224 p303 p387 p657 : Prop)
    (h26867 : p387 ∨ p303)
    (h26886 : (¬ p224) ∨ (¬ p657))
    (h13326 : (¬ p4) ∨ (¬ p387) ∨ p657) : p303 ∨ (¬ p224) ∨ (¬ p4) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : (¬ p657) := by
    rcases h26886 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h13326 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (u4 q2)

theorem step28877 (p4 p8 p125 p310 p710 : Prop)
    (h26888 : (¬ p8) ∨ (¬ p710))
    (h15189 : (¬ p4) ∨ (¬ p125) ∨ (¬ p310) ∨ p710) : (¬ p125) ∨ (¬ p8) ∨ (¬ p4) ∨ (¬ p310) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p710) := by
    rcases h26888 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h15189 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (u4 q3)

theorem step28880 (p4 p110 p124 p125 p225 p544 : Prop)
    (h26877 : p544 ∨ p225)
    (h18329 : (¬ p4) ∨ (¬ p110) ∨ (¬ p124) ∨ (¬ p125) ∨ (¬ p544)) : (¬ p125) ∨ p225 ∨ (¬ p4) ∨ (¬ p124) ∨ (¬ p110) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18329 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)

theorem step28881 (p4 p124 p126 p224 p258 p261 p288 p301 p304 : Prop)
    (h26859 : p304 ∨ p124)
    (h26857 : p301 ∨ p126)
    (h26855 : p288 ∨ p258)
    (h20102 : (¬ p4) ∨ (¬ p224) ∨ (¬ p261) ∨ (¬ p288) ∨ (¬ p301) ∨ (¬ p304)) : p124 ∨ p126 ∨ (¬ p224) ∨ (¬ p261) ∨ (¬ p4) ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20102 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u6)

theorem step28882 (p4 p126 p287 p836 p840 : Prop)
    (h26895 : p840 ∨ p836)
    (h11584 : (¬ p4) ∨ p126 ∨ (¬ p287) ∨ (¬ p840)) : p126 ∨ (¬ p4) ∨ (¬ p287) ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h11584 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step28883 (p4 p224 p364 p382 p406 : Prop)
    (h26869 : p406 ∨ p382)
    (h12803 : (¬ p4) ∨ (¬ p224) ∨ (¬ p364) ∨ (¬ p406)) : (¬ p364) ∨ p382 ∨ (¬ p4) ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p364 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h12803 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)

theorem step28884 (p4 p110 p225 p420 p544 p633 : Prop)
    (h26877 : p544 ∨ p225)
    (h19456 : (¬ p4) ∨ (¬ p110) ∨ (¬ p420) ∨ (¬ p544) ∨ (¬ p633)) : (¬ p420) ∨ p225 ∨ (¬ p4) ∨ (¬ p633) ∨ (¬ p110) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19456 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)

theorem step28885 (p4 p10 p101 p102 p668 p1076 p1077 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26837 : p102 ∨ p101)
    (h16660 : (¬ p4) ∨ (¬ p10) ∨ (¬ p102) ∨ (¬ p668) ∨ (¬ p1077)) : (¬ p10) ∨ (¬ p4) ∨ (¬ p668) ∨ p1076 ∨ p101 := by
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
  have u2 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16660 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step28886 (p4 p12 p225 p303 p387 p544 p1036 : Prop)
    (h26907 : p1036 ∨ p12)
    (h26877 : p544 ∨ p225)
    (h26867 : p387 ∨ p303)
    (h25870 : (¬ p387) ∨ (¬ p544) ∨ (¬ p4) ∨ (¬ p1036)) : p12 ∨ p225 ∨ (¬ p4) ∨ p303 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p12) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h25870 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step28887 (p4 p420 p640 p897 p904 : Prop)
    (h26899 : p904 ∨ p897)
    (h12620 : (¬ p4) ∨ (¬ p420) ∨ (¬ p640) ∨ (¬ p904)) : (¬ p420) ∨ p897 ∨ (¬ p640) ∨ (¬ p4) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p897) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p640 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h12620 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step28888 (p4 p306 p420 p633 p668 p1055 p1061 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h20294 : (¬ p4) ∨ (¬ p306) ∨ (¬ p420) ∨ (¬ p633) ∨ (¬ p668) ∨ (¬ p1061)) : (¬ p420) ∨ p1055 ∨ (¬ p668) ∨ (¬ p306) ∨ (¬ p633) ∨ (¬ p4) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20294 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)

theorem step28890 (p6 p24 p67 p234 p344 p346 p534 p539 p633 p636 p738 : Prop)
    (h26863 : p346 ∨ p344)
    (h26885 : p636 ∨ p633)
    (h17993 : (¬ p6) ∨ (¬ p24) ∨ (¬ p67) ∨ (¬ p234) ∨ (¬ p346) ∨ (¬ p534) ∨ (¬ p539) ∨ (¬ p636) ∨ (¬ p738)) : (¬ p534) ∨ (¬ p738) ∨ (¬ p539) ∨ (¬ p67) ∨ (¬ p24) ∨ (¬ p6) ∨ (¬ p234) ∨ p344 ∨ p633 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p738 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p539 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p633) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h17993 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u1)

theorem step28891 (p12 p17 p88 p534 p758 p924 p1036 p1055 p1061 p1098 p1644 : Prop)
    (h26907 : p1036 ∨ p12)
    (h26909 : p1061 ∨ p1055)
    (h20479 : (¬ p17) ∨ (¬ p88) ∨ (¬ p534) ∨ (¬ p758) ∨ (¬ p924) ∨ (¬ p1036) ∨ (¬ p1061) ∨ (¬ p1098) ∨ (¬ p1644)) : (¬ p758) ∨ (¬ p534) ∨ (¬ p1098) ∨ (¬ p17) ∨ p12 ∨ (¬ p924) ∨ (¬ p88) ∨ (¬ p1644) ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p758 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1098 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1644 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h20479 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u2)
  · exact False.elim (q8 u7)

theorem step28892 (p185 p189 p193 p534 p1584 : Prop)
    (h26845 : p193 ∨ p189)
    (h18282 : (¬ p185) ∨ (¬ p193) ∨ (¬ p534) ∨ (¬ p1584)) : (¬ p534) ∨ (¬ p185) ∨ p189 ∨ (¬ p1584) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18282 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)

theorem step28893 (p41 p104 p344 p346 p534 p1586 p1772 : Prop)
    (h26863 : p346 ∨ p344)
    (h19717 : (¬ p41) ∨ (¬ p104) ∨ (¬ p346) ∨ (¬ p534) ∨ (¬ p1586) ∨ (¬ p1772)) : (¬ p1586) ∨ (¬ p1772) ∨ (¬ p41) ∨ (¬ p104) ∨ (¬ p534) ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1586 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1772 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19717 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u1)

theorem step28894 (p11 p12 p84 p227 p258 p266 p288 p534 p929 p1036 p1538 : Prop)
    (h26855 : p288 ∨ p258)
    (h26907 : p1036 ∨ p12)
    (h18208 : (¬ p11) ∨ (¬ p84) ∨ (¬ p227) ∨ (¬ p266) ∨ (¬ p288) ∨ (¬ p534) ∨ (¬ p929) ∨ (¬ p1036) ∨ (¬ p1538)) : (¬ p534) ∨ (¬ p11) ∨ p258 ∨ p12 ∨ (¬ p929) ∨ (¬ p266) ∨ (¬ p227) ∨ (¬ p1538) ∨ (¬ p84) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1538 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18208 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u7)

theorem step28895 (p163 p189 p193 p382 p406 p534 p690 p735 p789 p858 : Prop)
    (h26869 : p406 ∨ p382)
    (h26845 : p193 ∨ p189)
    (h26897 : p858 ∨ p789)
    (h17797 : (¬ p163) ∨ (¬ p193) ∨ (¬ p406) ∨ (¬ p534) ∨ (¬ p690) ∨ (¬ p735) ∨ (¬ p858)) : (¬ p534) ∨ (¬ p735) ∨ p382 ∨ (¬ p163) ∨ p189 ∨ p789 ∨ (¬ p690) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p735 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17797 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u9)

theorem step28901 (p17 p189 p193 p309 p382 p419 p540 p709 p734 p752 p996 p1644 : Prop)
    (h26905 : p996 ∨ p419)
    (h26845 : p193 ∨ p189)
    (h17945 : (¬ p17) ∨ (¬ p193) ∨ (¬ p309) ∨ (¬ p382) ∨ (¬ p540) ∨ (¬ p709) ∨ (¬ p734) ∨ (¬ p752) ∨ (¬ p996) ∨ (¬ p1644)) : (¬ p1644) ∨ (¬ p734) ∨ p419 ∨ (¬ p540) ∨ (¬ p309) ∨ (¬ p752) ∨ (¬ p17) ∨ p189 ∨ (¬ p382) ∨ (¬ p709) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1644 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p540 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p752 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p709 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h17945 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u11)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u10)
  · exact False.elim (q9 u0)

theorem step28902 (p303 p345 p368 p382 p406 p752 p1624 : Prop)
    (h26869 : p406 ∨ p382)
    (h19764 : (¬ p303) ∨ (¬ p345) ∨ (¬ p368) ∨ (¬ p406) ∨ (¬ p752) ∨ (¬ p1624)) : (¬ p1624) ∨ p382 ∨ (¬ p752) ∨ (¬ p345) ∨ (¬ p303) ∨ (¬ p368) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1624 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p752 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p345 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19764 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u0)

theorem step28904 (p3 p14 p226 p234 p303 p331 p382 p406 p519 p576 p581 p816 p1187 : Prop)
    (h26847 : p226 ∨ p3)
    (h26879 : p581 ∨ p576)
    (h26869 : p406 ∨ p382)
    (h26921 : p1187 ∨ p234)
    (h20558 : (¬ p14) ∨ (¬ p226) ∨ (¬ p303) ∨ (¬ p331) ∨ (¬ p406) ∨ (¬ p519) ∨ (¬ p581) ∨ (¬ p816) ∨ (¬ p1187)) : p3 ∨ p576 ∨ (¬ p519) ∨ (¬ p303) ∨ (¬ p331) ∨ p382 ∨ (¬ p816) ∨ p234 ∨ (¬ p14) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p519 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p331 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p816 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p234) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u11 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u12 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h20558 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u12)

theorem step28905 (p225 p542 p544 : Prop)
    (h26877 : p544 ∨ p225)
    (h21013 : p542 ∨ (¬ p544)) : p542 ∨ p225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p542) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr hu)
  have u2 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h21013 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)

theorem step28906 (p225 p544 p563 : Prop)
    (h26877 : p544 ∨ p225)
    (h19098 : (¬ p544) ∨ p563) : p225 ∨ p563 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p225) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p563) := fun hu => hn (Or.inr hu)
  have u2 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19098 with q0 | q1
  · exact False.elim (q0 u2)
  · exact False.elim (u1 q1)

theorem step28908 (p14 p225 p544 p836 p1115 p1116 : Prop)
    (h26877 : p544 ∨ p225)
    (h26915 : p1116 ∨ p1115)
    (h17302 : (¬ p14) ∨ (¬ p544) ∨ (¬ p836) ∨ (¬ p1116)) : (¬ p836) ∨ p225 ∨ p1115 ∨ (¬ p14) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17302 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)

theorem step28910 (p169 p225 p544 p836 : Prop)
    (h26877 : p544 ∨ p225)
    (h14458 : (¬ p169) ∨ (¬ p544) ∨ (¬ p836)) : (¬ p836) ∨ p225 ∨ (¬ p169) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p169 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h14458 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)

theorem step28912 (p163 p224 p225 p424 p544 p657 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h26887 : p657 ∨ p224)
    (h26877 : p544 ∨ p225)
    (h19540 : (¬ p163) ∨ (¬ p544) ∨ (¬ p657) ∨ (¬ p796)) : p424 ∨ (¬ p163) ∨ p224 ∨ p225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19540 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step28913 (p163 p224 p225 p544 p657 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26877 : p544 ∨ p225)
    (h26887 : p657 ∨ p224)
    (h19567 : (¬ p163) ∨ (¬ p544) ∨ (¬ p657) ∨ (¬ p1333)) : p1325 ∨ p225 ∨ p224 ∨ (¬ p163) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1325) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19567 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)

theorem step28914 (p12 p185 p225 p544 p836 p1036 : Prop)
    (h26877 : p544 ∨ p225)
    (h26907 : p1036 ∨ p12)
    (h19935 : (¬ p185) ∨ (¬ p544) ∨ (¬ p836) ∨ (¬ p1036)) : p225 ∨ (¬ p836) ∨ p12 ∨ (¬ p185) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p225) := fun hu => hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19935 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)

theorem step28915 (p14 p225 p344 p346 p544 p1076 p1077 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26863 : p346 ∨ p344)
    (h26877 : p544 ∨ p225)
    (h17991 : (¬ p14) ∨ (¬ p346) ∨ (¬ p544) ∨ (¬ p1077)) : p1076 ∨ p344 ∨ (¬ p14) ∨ p225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1076) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17991 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)

theorem step28916 (p14 p15 p225 p382 p544 p621 p789 p842 : Prop)
    (h26877 : p544 ∨ p225)
    (h19095 : (¬ p14) ∨ (¬ p15) ∨ (¬ p382) ∨ (¬ p544) ∨ (¬ p621) ∨ (¬ p789) ∨ (¬ p842)) : (¬ p789) ∨ (¬ p621) ∨ (¬ p842) ∨ (¬ p382) ∨ (¬ p14) ∨ (¬ p15) ∨ p225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p621 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p842 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19095 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u2)

theorem step28918 (p14 p18 p225 p344 p346 p544 : Prop)
    (h26877 : p544 ∨ p225)
    (h26863 : p346 ∨ p344)
    (h18826 : (¬ p14) ∨ (¬ p18) ∨ (¬ p346) ∨ (¬ p544)) : p225 ∨ (¬ p14) ∨ (¬ p18) ∨ p344 := by
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
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18826 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step28919 (p41 p63 p163 p225 p544 : Prop)
    (h26877 : p544 ∨ p225)
    (h17820 : (¬ p41) ∨ (¬ p63) ∨ (¬ p163) ∨ (¬ p544)) : p225 ∨ (¬ p41) ∨ (¬ p163) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p225) := fun hu => hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17820 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step28920 (p163 p225 p422 p544 p664 p1038 : Prop)
    (h26877 : p544 ∨ p225)
    (h17098 : (¬ p163) ∨ (¬ p422) ∨ (¬ p544) ∨ (¬ p664) ∨ (¬ p1038)) : (¬ p422) ∨ (¬ p1038) ∨ (¬ p664) ∨ (¬ p163) ∨ p225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1038 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17098 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u1)

theorem step28924 (p3 p225 p344 p346 p544 p1076 p1077 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26863 : p346 ∨ p344)
    (h26877 : p544 ∨ p225)
    (h17896 : (¬ p3) ∨ (¬ p346) ∨ (¬ p544) ∨ (¬ p1077)) : p1076 ∨ p344 ∨ (¬ p3) ∨ p225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1076) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17896 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)

theorem step28926 (p110 p225 p345 p438 p544 p728 : Prop)
    (h26877 : p544 ∨ p225)
    (h16643 : (¬ p110) ∨ (¬ p345) ∨ (¬ p438) ∨ (¬ p544) ∨ (¬ p728)) : (¬ p728) ∨ p225 ∨ (¬ p438) ∨ (¬ p345) ∨ (¬ p110) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p345 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16643 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)

theorem step28927 (p104 p124 p225 p263 p544 p728 p1330 p1349 p1489 : Prop)
    (h26877 : p544 ∨ p225)
    (h20231 : (¬ p104) ∨ (¬ p124) ∨ (¬ p263) ∨ (¬ p544) ∨ (¬ p728) ∨ (¬ p1330) ∨ (¬ p1349) ∨ (¬ p1489)) : (¬ p728) ∨ (¬ p104) ∨ (¬ p1349) ∨ p225 ∨ (¬ p1330) ∨ (¬ p263) ∨ (¬ p1489) ∨ (¬ p124) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p263 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20231 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u6)

theorem step28928 (p3 p6 p225 p344 p346 p544 : Prop)
    (h26877 : p544 ∨ p225)
    (h26863 : p346 ∨ p344)
    (h20559 : (¬ p3) ∨ (¬ p6) ∨ (¬ p346) ∨ (¬ p544)) : (¬ p3) ∨ p225 ∨ p344 ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20559 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step28930 (p185 p225 p237 p537 p544 p940 : Prop)
    (h26851 : p237 ∨ p185)
    (h26877 : p544 ∨ p225)
    (h17384 : (¬ p237) ∨ (¬ p537) ∨ (¬ p544) ∨ (¬ p940)) : (¬ p940) ∨ (¬ p537) ∨ p185 ∨ p225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17384 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)

theorem step28931 (p163 p189 p193 p225 p544 p728 : Prop)
    (h26877 : p544 ∨ p225)
    (h26845 : p193 ∨ p189)
    (h16769 : (¬ p163) ∨ (¬ p193) ∨ (¬ p544) ∨ (¬ p728)) : (¬ p728) ∨ p225 ∨ (¬ p163) ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16769 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step28932 (p163 p189 p193 p224 p225 p544 p657 : Prop)
    (h26887 : p657 ∨ p224)
    (h26877 : p544 ∨ p225)
    (h26845 : p193 ∨ p189)
    (h20146 : (¬ p163) ∨ (¬ p193) ∨ (¬ p544) ∨ (¬ p657)) : p224 ∨ p225 ∨ p189 ∨ (¬ p163) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p224) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20146 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step28935 (p3 p16 p71 p225 p544 p728 p1330 p1349 p1489 : Prop)
    (h26877 : p544 ∨ p225)
    (h20544 : (¬ p3) ∨ (¬ p16) ∨ (¬ p71) ∨ (¬ p544) ∨ (¬ p728) ∨ (¬ p1330) ∨ (¬ p1349) ∨ (¬ p1489)) : (¬ p728) ∨ (¬ p71) ∨ (¬ p1489) ∨ (¬ p16) ∨ (¬ p1330) ∨ (¬ p1349) ∨ (¬ p3) ∨ p225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h20544 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u2)

theorem step28937 (p3 p41 p187 p224 p225 p544 p657 : Prop)
    (h26877 : p544 ∨ p225)
    (h26887 : p657 ∨ p224)
    (h20156 : (¬ p3) ∨ (¬ p41) ∨ (¬ p187) ∨ (¬ p544) ∨ (¬ p657)) : (¬ p3) ∨ p225 ∨ p224 ∨ (¬ p41) ∨ (¬ p187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20156 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)

theorem step28938 (p185 p189 p193 p225 p544 p836 : Prop)
    (h26877 : p544 ∨ p225)
    (h26845 : p193 ∨ p189)
    (h17650 : (¬ p185) ∨ (¬ p193) ∨ (¬ p544) ∨ (¬ p836)) : (¬ p836) ∨ p225 ∨ (¬ p185) ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17650 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step28939 (p41 p45 p169 p225 p344 p346 p544 p918 p928 : Prop)
    (h26877 : p544 ∨ p225)
    (h26901 : p928 ∨ p918)
    (h26831 : p45 ∨ p41)
    (h26863 : p346 ∨ p344)
    (h19303 : (¬ p45) ∨ (¬ p169) ∨ (¬ p346) ∨ (¬ p544) ∨ (¬ p928)) : p225 ∨ p918 ∨ p41 ∨ (¬ p169) ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p225) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p169 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p544 := by
    rcases h26877 with q0 | q1
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
  have u8 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19303 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)

theorem step28940 (p3 p17 p83 p225 p544 p576 p581 p842 p1385 : Prop)
    (h26879 : p581 ∨ p576)
    (h26877 : p544 ∨ p225)
    (h25871 : (¬ p83) ∨ (¬ p581) ∨ (¬ p17) ∨ (¬ p842) ∨ (¬ p3) ∨ (¬ p1385) ∨ (¬ p544)) : (¬ p1385) ∨ p576 ∨ (¬ p842) ∨ (¬ p17) ∨ (¬ p83) ∨ p225 ∨ (¬ p3) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p842 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h25871 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u8)

theorem step28941 (p86 p163 p189 p193 p225 p544 p595 p616 p1287 p1325 : Prop)
    (h26877 : p544 ∨ p225)
    (h26845 : p193 ∨ p189)
    (h26883 : p616 ∨ p595)
    (h18100 : (¬ p86) ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p544) ∨ (¬ p616) ∨ (¬ p1287) ∨ (¬ p1325)) : p225 ∨ p189 ∨ p595 ∨ (¬ p163) ∨ (¬ p1287) ∨ (¬ p1325) ∨ (¬ p86) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p225) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18100 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step28942 (p163 p189 p193 p225 p303 p434 p544 p690 p821 : Prop)
    (h26845 : p193 ∨ p189)
    (h26877 : p544 ∨ p225)
    (h18756 : (¬ p163) ∨ (¬ p193) ∨ (¬ p303) ∨ (¬ p434) ∨ (¬ p544) ∨ (¬ p690) ∨ (¬ p821)) : (¬ p434) ∨ (¬ p690) ∨ (¬ p303) ∨ (¬ p821) ∨ (¬ p163) ∨ p189 ∨ p225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p821 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u8 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18756 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u3)

theorem step28943 (p134 p163 p225 p344 p346 p544 : Prop)
    (h26863 : p346 ∨ p344)
    (h26877 : p544 ∨ p225)
    (h19791 : (¬ p134) ∨ (¬ p163) ∨ (¬ p346) ∨ (¬ p544)) : p344 ∨ p225 ∨ (¬ p163) ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p344) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19791 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step28945 (p3 p11 p39 p68 p88 p126 p225 p261 p301 p351 p544 p961 p1443 : Prop)
    (h26935 : p1443 ∨ p11)
    (h26857 : p301 ∨ p126)
    (h26877 : p544 ∨ p225)
    (h19143 : (¬ p3) ∨ (¬ p39) ∨ (¬ p68) ∨ (¬ p88) ∨ (¬ p261) ∨ (¬ p301) ∨ (¬ p351) ∨ (¬ p544) ∨ (¬ p961) ∨ (¬ p1443)) : (¬ p961) ∨ p11 ∨ p126 ∨ (¬ p351) ∨ p225 ∨ (¬ p39) ∨ (¬ p3) ∨ (¬ p68) ∨ (¬ p261) ∨ (¬ p88) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p11) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p126) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u11 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u12 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19143 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u12)
  · exact False.elim (q8 u0)
  · exact False.elim (q9 u10)

theorem step28946 (p135 p169 p185 p189 p225 p237 p258 p544 p664 p1076 : Prop)
    (h26877 : p544 ∨ p225)
    (h26851 : p237 ∨ p185)
    (h19324 : (¬ p135) ∨ (¬ p169) ∨ (¬ p189) ∨ (¬ p237) ∨ (¬ p258) ∨ (¬ p544) ∨ (¬ p664) ∨ (¬ p1076)) : p225 ∨ p185 ∨ (¬ p1076) ∨ (¬ p189) ∨ (¬ p664) ∨ (¬ p135) ∨ (¬ p169) ∨ (¬ p258) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p225) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p169 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19324 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u2)

theorem step28947 (p41 p169 p185 p189 p225 p237 p544 : Prop)
    (h26851 : p237 ∨ p185)
    (h26877 : p544 ∨ p225)
    (h16247 : (¬ p41) ∨ (¬ p169) ∨ (¬ p189) ∨ (¬ p237) ∨ (¬ p544)) : p185 ∨ (¬ p41) ∨ p225 ∨ (¬ p169) ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p185) := fun hu => hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p169 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16247 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)

theorem step28948 (p12 p225 p544 p980 p1036 p1325 p1333 : Prop)
    (h26877 : p544 ∨ p225)
    (h26931 : p1333 ∨ p1325)
    (h26907 : p1036 ∨ p12)
    (h19163 : (¬ p544) ∨ (¬ p980) ∨ (¬ p1036) ∨ (¬ p1333)) : p225 ∨ p1325 ∨ p12 ∨ (¬ p980) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p225) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19163 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)

theorem step28949 (p12 p185 p225 p237 p544 p1036 p1115 p1116 : Prop)
    (h26877 : p544 ∨ p225)
    (h26907 : p1036 ∨ p12)
    (h26915 : p1116 ∨ p1115)
    (h26851 : p237 ∨ p185)
    (h19099 : (¬ p237) ∨ (¬ p544) ∨ (¬ p1036) ∨ (¬ p1116)) : p225 ∨ p12 ∨ p1115 ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p225) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19099 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)

theorem step28950 (p8 p110 p225 p544 p710 p1055 p1061 p1076 : Prop)
    (h26877 : p544 ∨ p225)
    (h26909 : p1061 ∨ p1055)
    (h26889 : p710 ∨ p8)
    (h17196 : (¬ p110) ∨ (¬ p544) ∨ (¬ p710) ∨ (¬ p1061) ∨ (¬ p1076)) : p225 ∨ p1055 ∨ (¬ p110) ∨ p8 ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p225) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17196 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u4)

theorem step28951 (p8 p225 p544 p710 p1055 p1061 p1074 : Prop)
    (h26877 : p544 ∨ p225)
    (h26909 : p1061 ∨ p1055)
    (h26889 : p710 ∨ p8)
    (h19553 : (¬ p544) ∨ (¬ p710) ∨ (¬ p1061) ∨ (¬ p1074)) : p225 ∨ p1055 ∨ p8 ∨ (¬ p1074) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p225) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p544 := by
    rcases h26877 with q0 | q1
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
  rcases h19553 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)

theorem step28952 (p3 p17 p135 p185 p187 p225 p256 p544 p664 p1115 : Prop)
    (h26853 : p256 ∨ p17)
    (h26877 : p544 ∨ p225)
    (h19332 : (¬ p3) ∨ (¬ p135) ∨ (¬ p185) ∨ (¬ p187) ∨ (¬ p256) ∨ (¬ p544) ∨ (¬ p664) ∨ (¬ p1115)) : (¬ p1115) ∨ (¬ p3) ∨ (¬ p664) ∨ (¬ p185) ∨ p17 ∨ (¬ p187) ∨ p225 ∨ (¬ p135) := by
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
  have u2 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19332 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u0)

theorem step28955 (p595 p836 p902 p917 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h16489 : (¬ p595) ∨ (¬ p836) ∨ (¬ p902) ∨ (¬ p917) ∨ (¬ p1099)) : (¬ p836) ∨ (¬ p917) ∨ (¬ p595) ∨ (¬ p902) ∨ p1096 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p917 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p902 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16489 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)

theorem step28956 (p8 p240 p710 p839 p902 p1022 p1545 : Prop)
    (h26889 : p710 ∨ p8)
    (h17137 : (¬ p240) ∨ (¬ p710) ∨ (¬ p839) ∨ (¬ p902) ∨ (¬ p1022) ∨ (¬ p1545)) : (¬ p1022) ∨ (¬ p902) ∨ (¬ p240) ∨ (¬ p1545) ∨ (¬ p839) ∨ p8 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p902 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p240 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p839 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17137 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u3)

theorem step28958 (p224 p657 p902 p1287 : Prop)
    (h26887 : p657 ∨ p224)
    (h8778 : (¬ p657) ∨ (¬ p902) ∨ (¬ p1287)) : (¬ p902) ∨ p224 ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p902 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h8778 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)

theorem step28962 (p495 p497 p499 p507 p508 p509 p510 p511 : Prop)
    (h26874 : (¬ p495) ∨ (¬ p499))
    (h2774 : p497 ∨ p499 ∨ (¬ p507) ∨ (¬ p508) ∨ (¬ p509) ∨ (¬ p510) ∨ (¬ p511)) : p497 ∨ (¬ p509) ∨ (¬ p511) ∨ (¬ p495) ∨ (¬ p508) ∨ (¬ p510) ∨ (¬ p507) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p497) := fun hu => hn (Or.inl hu)
  have u1 : p509 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p511 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p510 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p507 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p499) := by
    rcases h26874 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h2774 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u2)

theorem step28966 (p495 p497 p499 p502 p503 p504 p505 p506 : Prop)
    (h26874 : (¬ p495) ∨ (¬ p499))
    (h2749 : p497 ∨ p499 ∨ (¬ p502) ∨ (¬ p503) ∨ (¬ p504) ∨ (¬ p505) ∨ (¬ p506)) : p497 ∨ (¬ p505) ∨ (¬ p495) ∨ (¬ p502) ∨ (¬ p503) ∨ (¬ p506) ∨ (¬ p504) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p497) := fun hu => hn (Or.inl hu)
  have u1 : p505 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p502 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p503 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p506 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p504 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p499) := by
    rcases h26874 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h2749 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u5)

theorem step28967 (p124 p304 p961 p1083 : Prop)
    (h26858 : (¬ p124) ∨ (¬ p304))
    (h14122 : p304 ∨ (¬ p961) ∨ (¬ p1083)) : (¬ p1083) ∨ (¬ p961) ∨ (¬ p124) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1083 := by
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
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p304) := by
    rcases h26858 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h14122 with q0 | q1 | q2
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)

theorem step28969 (p224 p382 p657 p819 p918 p928 p1385 : Prop)
    (h26901 : p928 ∨ p918)
    (h26887 : p657 ∨ p224)
    (h18677 : (¬ p382) ∨ (¬ p657) ∨ (¬ p819) ∨ (¬ p928) ∨ (¬ p1385)) : p918 ∨ (¬ p819) ∨ p224 ∨ (¬ p382) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p918) := fun hu => hn (Or.inl hu)
  have u1 : p819 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18677 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)

theorem step28978 (p344 p455 p456 p633 p664 p1079 : Prop)
    (h26871 : p456 ∨ p455)
    (h19310 : (¬ p344) ∨ (¬ p456) ∨ (¬ p633) ∨ (¬ p664) ∨ (¬ p1079)) : p455 ∨ (¬ p1079) ∨ (¬ p664) ∨ (¬ p633) ∨ (¬ p344) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : p1079 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19310 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u1)

theorem step28979 (p15 p121 p455 p456 p495 : Prop)
    (h26871 : p456 ∨ p455)
    (h16381 : (¬ p15) ∨ (¬ p121) ∨ (¬ p456) ∨ (¬ p495)) : (¬ p15) ∨ p455 ∨ (¬ p121) ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p455) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16381 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)

theorem step28981 (p227 p421 p455 p456 : Prop)
    (h26871 : p456 ∨ p455)
    (h10102 : (¬ p227) ∨ (¬ p421) ∨ (¬ p456)) : p455 ∨ (¬ p421) ∨ (¬ p227) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h10102 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)

theorem step28983 (p455 p456 p495 p499 p633 p1096 : Prop)
    (h26871 : p456 ∨ p455)
    (h26874 : (¬ p495) ∨ (¬ p499))
    (h20943 : (¬ p456) ∨ (¬ p633) ∨ p499 ∨ (¬ p1096)) : p455 ∨ (¬ p1096) ∨ (¬ p633) ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : (¬ p499) := by
    rcases h26874 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h20943 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)

theorem step28985 (p24 p101 p102 p455 p456 p532 p1325 p1333 : Prop)
    (h26871 : p456 ∨ p455)
    (h26931 : p1333 ∨ p1325)
    (h26837 : p102 ∨ p101)
    (h16715 : (¬ p24) ∨ (¬ p102) ∨ (¬ p456) ∨ (¬ p532) ∨ (¬ p1333)) : p455 ∨ p1325 ∨ (¬ p24) ∨ (¬ p532) ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16715 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)

theorem step28987 (p11 p17 p256 p455 p456 p633 p1443 : Prop)
    (h26871 : p456 ∨ p455)
    (h26935 : p1443 ∨ p11)
    (h26853 : p256 ∨ p17)
    (h16788 : (¬ p256) ∨ (¬ p456) ∨ (¬ p633) ∨ (¬ p1443)) : p455 ∨ p11 ∨ p17 ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p11) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16788 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)

theorem step28989 (p11 p258 p455 p456 p495 p1443 : Prop)
    (h26871 : p456 ∨ p455)
    (h26935 : p1443 ∨ p11)
    (h18032 : (¬ p258) ∨ (¬ p456) ∨ (¬ p495) ∨ (¬ p1443)) : p455 ∨ (¬ p258) ∨ p11 ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18032 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)

theorem step28991 (p24 p121 p455 p456 p1206 : Prop)
    (h26871 : p456 ∨ p455)
    (h26922 : (¬ p121) ∨ (¬ p1206))
    (h12239 : (¬ p24) ∨ (¬ p456) ∨ p1206) : p455 ∨ (¬ p24) ∨ (¬ p121) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : (¬ p1206) := by
    rcases h26922 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h12239 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (u4 q2)

theorem step28994 (p101 p121 p455 p456 p495 : Prop)
    (h26871 : p456 ∨ p455)
    (h18412 : (¬ p101) ∨ (¬ p121) ∨ (¬ p456) ∨ (¬ p495)) : p455 ∨ (¬ p121) ∨ (¬ p495) ∨ (¬ p101) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h18412 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)

theorem step28998 (p125 p227 p455 p456 p633 : Prop)
    (h26871 : p456 ∨ p455)
    (h24187 : (¬ p125) ∨ (¬ p633) ∨ (¬ p227) ∨ (¬ p456)) : p455 ∨ (¬ p125) ∨ (¬ p633) ∨ (¬ p227) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h24187 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step28999 (p2 p41 p124 p187 p304 p389 p419 p455 p456 p481 p633 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h26859 : p304 ∨ p124)
    (h26871 : p456 ∨ p455)
    (h26873 : p481 ∨ p2)
    (h20293 : (¬ p41) ∨ (¬ p187) ∨ (¬ p304) ∨ (¬ p389) ∨ (¬ p456) ∨ (¬ p481) ∨ (¬ p633) ∨ (¬ p996)) : p419 ∨ p124 ∨ p455 ∨ (¬ p187) ∨ (¬ p633) ∨ (¬ p41) ∨ p2 ∨ (¬ p389) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p455) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20293 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u8)

theorem step29003 (p303 p382 p406 p537 p680 p769 : Prop)
    (h26869 : p406 ∨ p382)
    (h19757 : (¬ p303) ∨ (¬ p406) ∨ (¬ p537) ∨ (¬ p680) ∨ (¬ p769)) : (¬ p769) ∨ (¬ p680) ∨ (¬ p303) ∨ (¬ p537) ∨ p382 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p769 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19757 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)

theorem step29004 (p17 p382 p406 p576 p581 p656 p897 p904 p1325 p1333 p1516 p1772 : Prop)
    (h26879 : p581 ∨ p576)
    (h26869 : p406 ∨ p382)
    (h26899 : p904 ∨ p897)
    (h26931 : p1333 ∨ p1325)
    (h19845 : (¬ p17) ∨ (¬ p406) ∨ (¬ p581) ∨ (¬ p656) ∨ (¬ p904) ∨ (¬ p1333) ∨ (¬ p1516) ∨ (¬ p1772)) : (¬ p1516) ∨ (¬ p1772) ∨ p576 ∨ p382 ∨ p897 ∨ (¬ p656) ∨ (¬ p17) ∨ p1325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1516 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1772 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p656 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h19845 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u1)

theorem step29008 (p303 p347 p368 p382 p406 p421 p537 p577 p836 p922 p1538 : Prop)
    (h26869 : p406 ∨ p382)
    (h18150 : (¬ p303) ∨ (¬ p347) ∨ (¬ p368) ∨ (¬ p406) ∨ (¬ p421) ∨ (¬ p537) ∨ (¬ p577) ∨ (¬ p836) ∨ (¬ p922) ∨ (¬ p1538)) : (¬ p537) ∨ (¬ p421) ∨ (¬ p836) ∨ (¬ p347) ∨ (¬ p1538) ∨ p382 ∨ (¬ p922) ∨ (¬ p303) ∨ (¬ p368) ∨ (¬ p577) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1538 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p922 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18150 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u2)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u4)

theorem step29010 (p63 p85 p303 p347 p382 p406 p617 p836 p918 : Prop)
    (h26869 : p406 ∨ p382)
    (h26835 : p85 ∨ p63)
    (h19906 : (¬ p85) ∨ (¬ p303) ∨ (¬ p347) ∨ (¬ p406) ∨ (¬ p617) ∨ (¬ p836) ∨ (¬ p918)) : p382 ∨ (¬ p918) ∨ (¬ p347) ∨ (¬ p617) ∨ (¬ p836) ∨ (¬ p303) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p617 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19906 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u1)

theorem step29012 (p124 p303 p304 p350 p368 p382 p406 : Prop)
    (h26869 : p406 ∨ p382)
    (h26859 : p304 ∨ p124)
    (h16176 : (¬ p303) ∨ (¬ p304) ∨ (¬ p350) ∨ (¬ p368) ∨ (¬ p406)) : p382 ∨ p124 ∨ (¬ p350) ∨ (¬ p303) ∨ (¬ p368) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16176 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)

theorem step29013 (p224 p244 p382 p406 p680 p836 : Prop)
    (h26869 : p406 ∨ p382)
    (h16517 : (¬ p224) ∨ (¬ p244) ∨ (¬ p406) ∨ (¬ p680) ∨ (¬ p836)) : p382 ∨ (¬ p836) ∨ (¬ p224) ∨ (¬ p244) ∨ (¬ p680) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p244 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h16517 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u1)

theorem step29014 (p224 p382 p406 p534 p680 p769 : Prop)
    (h26869 : p406 ∨ p382)
    (h17472 : (¬ p224) ∨ (¬ p406) ∨ (¬ p534) ∨ (¬ p680) ∨ (¬ p769)) : (¬ p769) ∨ (¬ p534) ∨ (¬ p224) ∨ p382 ∨ (¬ p680) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p769 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17472 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u0)

theorem step29015 (p121 p134 p189 p224 p351 p382 p386 p406 p817 p1206 : Prop)
    (h26869 : p406 ∨ p382)
    (h26923 : p1206 ∨ p121)
    (h19980 : (¬ p134) ∨ (¬ p189) ∨ (¬ p224) ∨ (¬ p351) ∨ (¬ p386) ∨ (¬ p406) ∨ (¬ p817) ∨ (¬ p1206)) : p382 ∨ p121 ∨ (¬ p817) ∨ (¬ p386) ∨ (¬ p224) ∨ (¬ p189) ∨ (¬ p351) ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p121) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p817 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p386 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19980 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u9)

theorem step29016 (p41 p45 p224 p382 p406 p816 p1385 p1393 : Prop)
    (h26869 : p406 ∨ p382)
    (h26933 : p1393 ∨ p1385)
    (h26831 : p45 ∨ p41)
    (h20221 : (¬ p45) ∨ (¬ p224) ∨ (¬ p406) ∨ (¬ p816) ∨ (¬ p1393)) : p382 ∨ p1385 ∨ (¬ p224) ∨ p41 ∨ (¬ p816) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1385) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p816 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
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
    · exact False.elim (u3 q1)
  rcases h20221 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u6)

theorem step29017 (p17 p258 p344 p346 p382 p406 p419 p542 p817 : Prop)
    (h26869 : p406 ∨ p382)
    (h26863 : p346 ∨ p344)
    (h17746 : (¬ p17) ∨ (¬ p258) ∨ (¬ p346) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p542) ∨ (¬ p817)) : (¬ p258) ∨ p382 ∨ (¬ p419) ∨ p344 ∨ (¬ p17) ∨ (¬ p817) ∨ (¬ p542) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p817 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17746 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u5)

theorem step29018 (p17 p135 p185 p187 p255 p256 p344 p346 p382 p406 p419 p475 p542 : Prop)
    (h26869 : p406 ∨ p382)
    (h26863 : p346 ∨ p344)
    (h26853 : p256 ∨ p17)
    (h17747 : (¬ p135) ∨ (¬ p185) ∨ (¬ p187) ∨ (¬ p255) ∨ (¬ p256) ∨ (¬ p346) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p475) ∨ (¬ p542)) : (¬ p255) ∨ p382 ∨ (¬ p187) ∨ (¬ p185) ∨ p344 ∨ (¬ p475) ∨ (¬ p135) ∨ (¬ p419) ∨ (¬ p542) ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p255 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p475 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u11 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u12 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h17747 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u12)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u8)

theorem step29019 (p344 p382 p406 p690 p728 : Prop)
    (h26869 : p406 ∨ p382)
    (h18027 : (¬ p344) ∨ (¬ p406) ∨ (¬ p690) ∨ (¬ p728)) : p382 ∨ (¬ p728) ∨ (¬ p344) ∨ (¬ p690) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h18027 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)

theorem step29021 (p10 p101 p102 p124 p267 p304 p382 p406 p517 p789 p820 p858 : Prop)
    (h26859 : p304 ∨ p124)
    (h26869 : p406 ∨ p382)
    (h26897 : p858 ∨ p789)
    (h26837 : p102 ∨ p101)
    (h20609 : (¬ p10) ∨ (¬ p102) ∨ (¬ p267) ∨ (¬ p304) ∨ (¬ p406) ∨ (¬ p517) ∨ (¬ p820) ∨ (¬ p858)) : (¬ p10) ∨ p124 ∨ p382 ∨ (¬ p820) ∨ (¬ p267) ∨ p789 ∨ p101 ∨ (¬ p517) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p820 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p267 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p517 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u11 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20609 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u11)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u10)

theorem step29023 (p382 p406 p615 p1287 : Prop)
    (h26869 : p406 ∨ p382)
    (h10621 : (¬ p406) ∨ (¬ p615) ∨ (¬ p1287)) : (¬ p615) ∨ p382 ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p615 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h10621 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)

theorem step29025 (p63 p303 p347 p382 p406 p615 p897 p1096 p1099 p1389 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26869 : p406 ∨ p382)
    (h19926 : (¬ p63) ∨ (¬ p303) ∨ (¬ p347) ∨ (¬ p406) ∨ (¬ p615) ∨ (¬ p897) ∨ (¬ p1099) ∨ (¬ p1389)) : (¬ p615) ∨ (¬ p1389) ∨ (¬ p303) ∨ (¬ p897) ∨ p1096 ∨ (¬ p347) ∨ p382 ∨ (¬ p63) := by
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
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19926 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u1)

theorem step29026 (p495 p499 p634 p1096 : Prop)
    (h26874 : (¬ p495) ∨ (¬ p499))
    (h10764 : p499 ∨ (¬ p634) ∨ (¬ p1096)) : (¬ p634) ∨ (¬ p495) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p634 := by
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
  rcases h10764 with q0 | q1 | q2
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)

theorem step29027 (p23 p101 p102 p634 p1074 p1076 p1077 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26837 : p102 ∨ p101)
    (h16657 : (¬ p23) ∨ (¬ p102) ∨ (¬ p634) ∨ (¬ p1074) ∨ (¬ p1077)) : p1076 ∨ (¬ p634) ∨ (¬ p1074) ∨ (¬ p23) ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1076) := fun hu => hn (Or.inl hu)
  have u1 : p634 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p23 := by
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
  rcases h16657 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step29028 (p306 p350 p420 p601 p634 p1055 p1061 p1074 : Prop)
    (h26881 : p601 ∨ p420)
    (h26909 : p1061 ∨ p1055)
    (h20360 : (¬ p306) ∨ (¬ p350) ∨ (¬ p601) ∨ (¬ p634) ∨ (¬ p1061) ∨ (¬ p1074)) : (¬ p306) ∨ (¬ p634) ∨ (¬ p350) ∨ (¬ p1074) ∨ p420 ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p634 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u7 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20360 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u3)

theorem step29030 (p15 p225 p495 p544 p634 p897 : Prop)
    (h26877 : p544 ∨ p225)
    (h19989 : (¬ p15) ∨ (¬ p495) ∨ (¬ p544) ∨ (¬ p634) ∨ (¬ p897)) : p225 ∨ (¬ p495) ∨ (¬ p897) ∨ (¬ p634) ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p225) := fun hu => hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p634 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19989 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)

theorem step29031 (p306 p350 p420 p536 p601 p634 p1538 : Prop)
    (h26881 : p601 ∨ p420)
    (h20361 : (¬ p306) ∨ (¬ p350) ∨ (¬ p536) ∨ (¬ p601) ∨ (¬ p634) ∨ (¬ p1538)) : (¬ p536) ∨ (¬ p634) ∨ p420 ∨ (¬ p1538) ∨ (¬ p350) ∨ (¬ p306) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p536 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p634 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1538 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20361 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u3)

theorem step29032 (p41 p45 p84 p135 p265 p419 p421 p431 p634 p734 p790 p801 p897 p996 : Prop)
    (h26831 : p45 ∨ p41)
    (h26905 : p996 ∨ p419)
    (h20292 : (¬ p45) ∨ (¬ p84) ∨ (¬ p135) ∨ (¬ p265) ∨ (¬ p421) ∨ (¬ p431) ∨ (¬ p634) ∨ (¬ p734) ∨ (¬ p790) ∨ (¬ p801) ∨ (¬ p897) ∨ (¬ p996)) : (¬ p634) ∨ (¬ p421) ∨ (¬ p801) ∨ (¬ p897) ∨ (¬ p84) ∨ (¬ p790) ∨ (¬ p265) ∨ p41 ∨ (¬ p734) ∨ p419 ∨ (¬ p431) ∨ (¬ p135) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p634 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p801 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))
  have u12 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u13 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h20292 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (q0 u12)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u2)
  · exact False.elim (q10 u3)
  · exact False.elim (q11 u13)

theorem step29035 (p455 p456 p462 p465 p466 p467 p468 p469 : Prop)
    (h26870 : (¬ p455) ∨ (¬ p456))
    (h2486 : p456 ∨ p462 ∨ (¬ p465) ∨ (¬ p466) ∨ (¬ p467) ∨ (¬ p468) ∨ (¬ p469)) : (¬ p469) ∨ (¬ p467) ∨ (¬ p455) ∨ (¬ p466) ∨ p462 ∨ (¬ p465) ∨ (¬ p468) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p469 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p467 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p466 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p462) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p468 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p456) := by
    rcases h26870 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h2486 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u7 q0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u0)

theorem step29037 (p455 p456 p464 p465 p466 p467 p468 p469 : Prop)
    (h26870 : (¬ p455) ∨ (¬ p456))
    (h2489 : p456 ∨ p464 ∨ (¬ p465) ∨ (¬ p466) ∨ (¬ p467) ∨ (¬ p468) ∨ (¬ p469)) : p464 ∨ (¬ p469) ∨ (¬ p455) ∨ (¬ p466) ∨ (¬ p467) ∨ (¬ p468) ∨ (¬ p465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p464) := fun hu => hn (Or.inl hu)
  have u1 : p469 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p466 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p467 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p468 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p456) := by
    rcases h26870 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h2489 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u7 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u1)

theorem step29038 (p17 p419 p790 p800 p857 p996 p1492 : Prop)
    (h26905 : p996 ∨ p419)
    (h18969 : (¬ p17) ∨ (¬ p790) ∨ (¬ p800) ∨ (¬ p857) ∨ (¬ p996) ∨ (¬ p1492)) : (¬ p800) ∨ p419 ∨ (¬ p790) ∨ (¬ p17) ∨ (¬ p1492) ∨ (¬ p857) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p800 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p419) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1492 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p857 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18969 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u4)

theorem step29040 (p303 p387 p517 p857 p1249 p1385 p1393 : Prop)
    (h26867 : p387 ∨ p303)
    (h26933 : p1393 ∨ p1385)
    (h17961 : (¬ p387) ∨ (¬ p517) ∨ (¬ p857) ∨ (¬ p1249) ∨ (¬ p1393)) : (¬ p517) ∨ p303 ∨ (¬ p1249) ∨ p1385 ∨ (¬ p857) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p517 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p857 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17961 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)

theorem step29041 (p224 p657 p789 p835 : Prop)
    (h26886 : (¬ p224) ∨ (¬ p657))
    (h14371 : p657 ∨ (¬ p789) ∨ (¬ p835)) : (¬ p789) ∨ (¬ p835) ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p835 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p657) := by
    rcases h26886 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h14371 with q0 | q1 | q2
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)

theorem step29044 (p668 p835 p918 p928 p1115 p1116 p1385 : Prop)
    (h26901 : p928 ∨ p918)
    (h26915 : p1116 ∨ p1115)
    (h20211 : (¬ p668) ∨ (¬ p835) ∨ (¬ p928) ∨ (¬ p1116) ∨ (¬ p1385)) : p918 ∨ (¬ p835) ∨ (¬ p668) ∨ (¬ p1385) ∨ p1115 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p918) := fun hu => hn (Or.inl hu)
  have u1 : p835 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20211 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)

theorem step29045 (p185 p237 p668 p790 p814 p835 p1115 p1116 : Prop)
    (h26893 : p814 ∨ p790)
    (h26851 : p237 ∨ p185)
    (h26915 : p1116 ∨ p1115)
    (h20415 : (¬ p237) ∨ (¬ p668) ∨ (¬ p814) ∨ (¬ p835) ∨ (¬ p1116)) : p790 ∨ p185 ∨ (¬ p668) ∨ (¬ p835) ∨ p1115 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p790) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p835 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20415 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u7)

theorem step29046 (p185 p237 p790 p814 p835 p897 p904 p917 : Prop)
    (h26893 : p814 ∨ p790)
    (h26899 : p904 ∨ p897)
    (h26851 : p237 ∨ p185)
    (h16228 : (¬ p237) ∨ (¬ p814) ∨ (¬ p835) ∨ (¬ p904) ∨ (¬ p917)) : p790 ∨ (¬ p835) ∨ p897 ∨ (¬ p917) ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p790) := fun hu => hn (Or.inl hu)
  have u1 : p835 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p917 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16228 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)

theorem step29047 (p185 p237 p286 p668 p790 p814 p835 p1076 p1077 : Prop)
    (h26893 : p814 ∨ p790)
    (h26851 : p237 ∨ p185)
    (h26911 : p1077 ∨ p1076)
    (h17487 : (¬ p237) ∨ (¬ p286) ∨ (¬ p668) ∨ (¬ p814) ∨ (¬ p835) ∨ (¬ p1077)) : p790 ∨ p185 ∨ (¬ p286) ∨ (¬ p835) ∨ p1076 ∨ (¬ p668) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p790) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p835 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17487 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u8)

theorem step29048 (p158 p668 p835 p918 p928 p1055 p1061 p1385 : Prop)
    (h26901 : p928 ∨ p918)
    (h26909 : p1061 ∨ p1055)
    (h20210 : (¬ p158) ∨ (¬ p668) ∨ (¬ p835) ∨ (¬ p928) ∨ (¬ p1061) ∨ (¬ p1385)) : p918 ∨ p1055 ∨ (¬ p158) ∨ (¬ p835) ∨ (¬ p1385) ∨ (¬ p668) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p918) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p835 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20210 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u4)

theorem step29049 (p185 p237 p285 p344 p790 p814 p835 : Prop)
    (h26893 : p814 ∨ p790)
    (h26851 : p237 ∨ p185)
    (h19705 : (¬ p237) ∨ (¬ p285) ∨ (¬ p344) ∨ (¬ p814) ∨ (¬ p835)) : p790 ∨ (¬ p835) ∨ (¬ p285) ∨ p185 ∨ (¬ p344) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p790) := fun hu => hn (Or.inl hu)
  have u1 : p835 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p285 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19705 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)

theorem step29051 (p24 p63 p125 p210 p431 p438 p633 p789 p1385 p1393 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h20569 : p24 ∨ (¬ p63) ∨ (¬ p125) ∨ (¬ p210) ∨ (¬ p431) ∨ (¬ p438) ∨ (¬ p633) ∨ (¬ p789) ∨ (¬ p1393)) : (¬ p125) ∨ p24 ∨ (¬ p431) ∨ (¬ p210) ∨ (¬ p633) ∨ (¬ p789) ∨ p1385 ∨ (¬ p438) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p24) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20569 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u9)

theorem step29053 (p290 p344 p346 p382 p713 p789 p839 : Prop)
    (h26863 : p346 ∨ p344)
    (h17586 : (¬ p290) ∨ (¬ p346) ∨ (¬ p382) ∨ (¬ p713) ∨ (¬ p789) ∨ (¬ p839)) : (¬ p789) ∨ (¬ p290) ∨ (¬ p382) ∨ (¬ p839) ∨ p344 ∨ (¬ p713) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p290 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p839 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p713 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17586 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u3)

theorem step29055 (p8 p710 p713 : Prop)
    (h26888 : (¬ p8) ∨ (¬ p710))
    (h20854 : p710 ∨ p713) : (¬ p8) ∨ p713 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p713) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p710) := by
    rcases h26888 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h20854 with q0 | q1
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)

theorem step29056 (p8 p306 p344 p346 p710 : Prop)
    (h26888 : (¬ p8) ∨ (¬ p710))
    (h26863 : p346 ∨ p344)
    (h13999 : (¬ p306) ∨ (¬ p346) ∨ p710) : (¬ p306) ∨ (¬ p8) ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : (¬ p710) := by
    rcases h26888 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  have u4 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h13999 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (u3 q2)

theorem step29060 (p8 p709 p710 p713 : Prop)
    (h26888 : (¬ p8) ∨ (¬ p710))
    (h20845 : p713 ∨ p709 ∨ p710) : (¬ p8) ∨ p713 ∨ p709 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p713) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p709) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : (¬ p710) := by
    rcases h26888 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h20845 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (u3 q2)

theorem step29061 (p8 p225 p557 p710 : Prop)
    (h26888 : (¬ p8) ∨ (¬ p710))
    (h14361 : (¬ p225) ∨ (¬ p557) ∨ p710) : (¬ p557) ∨ (¬ p8) ∨ (¬ p225) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p710) := by
    rcases h26888 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h14361 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (u3 q2)

theorem step29068 (p308 p1055 p1061 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h17340 : p308 ∨ (¬ p1061)) : p308 ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p308) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr hu)
  have u2 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17340 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)

theorem step29069 (p690 p709 p728 p1055 p1061 p1076 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h17374 : (¬ p690) ∨ (¬ p709) ∨ (¬ p728) ∨ (¬ p1061) ∨ (¬ p1076)) : (¬ p728) ∨ p1055 ∨ (¬ p690) ∨ (¬ p709) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p709 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17374 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)

theorem step29071 (p104 p557 p1055 p1061 p1076 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h12197 : (¬ p104) ∨ (¬ p557) ∨ (¬ p1061) ∨ (¬ p1076)) : (¬ p104) ∨ (¬ p557) ∨ (¬ p1076) ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h12197 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)

theorem step29072 (p14 p18 p557 p1055 p1061 p1076 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h17198 : (¬ p14) ∨ (¬ p18) ∨ (¬ p557) ∨ (¬ p1061) ∨ (¬ p1076)) : p1055 ∨ (¬ p557) ∨ (¬ p14) ∨ (¬ p1076) ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1055) := fun hu => hn (Or.inl hu)
  have u1 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17198 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)

theorem step29074 (p134 p163 p557 p1055 p1061 p1076 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h17553 : (¬ p134) ∨ (¬ p163) ∨ (¬ p557) ∨ (¬ p1061) ∨ (¬ p1076)) : (¬ p557) ∨ (¬ p1076) ∨ (¬ p134) ∨ p1055 ∨ (¬ p163) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17553 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)

theorem step29075 (p163 p344 p557 p1055 p1061 p1076 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h17559 : (¬ p163) ∨ (¬ p344) ∨ (¬ p557) ∨ (¬ p1061) ∨ (¬ p1076)) : (¬ p344) ∨ (¬ p1076) ∨ p1055 ∨ (¬ p163) ∨ (¬ p557) := by
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
  have u2 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17559 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)

theorem step29076 (p306 p1055 p1061 p1076 p1077 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h26910 : (¬ p1076) ∨ (¬ p1077))
    (h10270 : (¬ p306) ∨ (¬ p1061) ∨ p1077) : (¬ p306) ∨ p1055 ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u4 : (¬ p1077) := by
    rcases h26910 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h10270 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (u4 q2)

theorem step29078 (p101 p102 p121 p312 p1055 p1061 p1079 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26837 : p102 ∨ p101)
    (h26909 : p1061 ∨ p1055)
    (h17616 : (¬ p102) ∨ (¬ p312) ∨ (¬ p1061) ∨ (¬ p1079) ∨ (¬ p1206)) : p121 ∨ (¬ p312) ∨ p101 ∨ (¬ p1079) ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p312 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1079 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17616 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)

theorem step29079 (p125 p310 p1055 p1061 p1076 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h24188 : (¬ p1061) ∨ (¬ p1076) ∨ (¬ p125) ∨ (¬ p310)) : p1055 ∨ (¬ p1076) ∨ (¬ p310) ∨ (¬ p125) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1055) := fun hu => hn (Or.inl hu)
  have u1 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h24188 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)

theorem step29080 (p258 p268 p310 p1055 p1061 p1076 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h16407 : (¬ p258) ∨ (¬ p268) ∨ (¬ p310) ∨ (¬ p1061) ∨ (¬ p1076)) : (¬ p258) ∨ (¬ p310) ∨ p1055 ∨ (¬ p268) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p268 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16407 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)

theorem step29081 (p41 p45 p63 p85 p110 p163 p167 p1055 p1061 p1076 : Prop)
    (h26831 : p45 ∨ p41)
    (h26835 : p85 ∨ p63)
    (h26843 : p167 ∨ p163)
    (h26909 : p1061 ∨ p1055)
    (h22725 : (¬ p45) ∨ (¬ p110) ∨ (¬ p1061) ∨ (¬ p1076) ∨ (¬ p167) ∨ (¬ p85)) : (¬ p110) ∨ p41 ∨ p63 ∨ (¬ p1076) ∨ p163 ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p41) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h22725 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u7)

theorem step29083 (p6 p18 p19 p561 p1055 p1061 p1076 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h26829 : p19 ∨ p18)
    (h17626 : (¬ p6) ∨ (¬ p19) ∨ (¬ p561) ∨ (¬ p1061) ∨ (¬ p1076)) : p1055 ∨ (¬ p561) ∨ (¬ p6) ∨ (¬ p1076) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1055) := fun hu => hn (Or.inl hu)
  have u1 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17626 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)

theorem step29084 (p11 p258 p288 p312 p1055 p1061 p1079 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h26855 : p288 ∨ p258)
    (h17614 : (¬ p11) ∨ (¬ p288) ∨ (¬ p312) ∨ (¬ p1061) ∨ (¬ p1079)) : (¬ p11) ∨ (¬ p312) ∨ p1055 ∨ (¬ p1079) ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p312 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1079 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17614 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)

theorem step29085 (p158 p255 p1055 p1061 p1076 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h12477 : (¬ p158) ∨ (¬ p255) ∨ (¬ p1061) ∨ (¬ p1076)) : (¬ p255) ∨ p1055 ∨ (¬ p158) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p255 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h12477 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)

theorem step29086 (p158 p344 p918 p928 p1055 p1061 p1076 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h26901 : p928 ∨ p918)
    (h17558 : (¬ p158) ∨ (¬ p344) ∨ (¬ p928) ∨ (¬ p1061) ∨ (¬ p1076)) : p1055 ∨ (¬ p344) ∨ (¬ p1076) ∨ p918 ∨ (¬ p158) := by
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
  have u3 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17558 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)

theorem step29088 (p15 p69 p234 p344 p545 p1055 p1061 p1076 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26833 : p69 ∨ p15)
    (h26909 : p1061 ∨ p1055)
    (h22726 : (¬ p545) ∨ (¬ p69) ∨ (¬ p344) ∨ (¬ p1061) ∨ (¬ p1076) ∨ (¬ p1187)) : p234 ∨ (¬ p545) ∨ p15 ∨ (¬ p1076) ∨ p1055 ∨ (¬ p344) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h22726 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)

theorem step29116 (p17 p89 p224 p256 p382 p576 p657 p709 p838 p1103 p1385 p1393 : Prop)
    (h26853 : p256 ∨ p17)
    (h26887 : p657 ∨ p224)
    (h26933 : p1393 ∨ p1385)
    (h18573 : (¬ p89) ∨ (¬ p256) ∨ (¬ p382) ∨ (¬ p576) ∨ (¬ p657) ∨ (¬ p709) ∨ (¬ p838) ∨ (¬ p1103) ∨ (¬ p1393)) : p17 ∨ (¬ p709) ∨ (¬ p576) ∨ (¬ p89) ∨ p224 ∨ p1385 ∨ (¬ p382) ∨ (¬ p838) ∨ (¬ p1103) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p17) := fun hu => hn (Or.inl hu)
  have u1 : p709 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p838 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18573 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u11)

theorem step29117 (p63 p126 p224 p347 p382 p576 p581 p657 p709 p1103 : Prop)
    (h26879 : p581 ∨ p576)
    (h26887 : p657 ∨ p224)
    (h18575 : (¬ p63) ∨ (¬ p126) ∨ (¬ p347) ∨ (¬ p382) ∨ (¬ p581) ∨ (¬ p657) ∨ (¬ p709) ∨ (¬ p1103)) : p576 ∨ (¬ p709) ∨ p224 ∨ (¬ p126) ∨ (¬ p63) ∨ (¬ p1103) ∨ (¬ p347) ∨ (¬ p382) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p576) := fun hu => hn (Or.inl hu)
  have u1 : p709 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18575 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u5)

theorem step29119 (p240 p400 p709 p980 p983 p1115 p1116 p1226 : Prop)
    (h26903 : p983 ∨ p980)
    (h26915 : p1116 ∨ p1115)
    (h19021 : (¬ p240) ∨ (¬ p400) ∨ (¬ p709) ∨ (¬ p983) ∨ (¬ p1116) ∨ (¬ p1226)) : (¬ p400) ∨ p980 ∨ (¬ p1226) ∨ p1115 ∨ (¬ p709) ∨ (¬ p240) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p400 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p709 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p240 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19021 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)

theorem step29123 (p595 p616 p622 p623 p624 p625 p626 p627 : Prop)
    (h26882 : (¬ p595) ∨ (¬ p616))
    (h3504 : p616 ∨ p622 ∨ (¬ p623) ∨ (¬ p624) ∨ (¬ p625) ∨ (¬ p626) ∨ (¬ p627)) : (¬ p624) ∨ (¬ p625) ∨ (¬ p595) ∨ p622 ∨ (¬ p627) ∨ (¬ p623) ∨ (¬ p626) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p624 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p625 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p622) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p627 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p623 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p626 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p616) := by
    rcases h26882 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h3504 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u7 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u4)

theorem step29125 (p595 p616 p1015 p1395 p1548 p1674 : Prop)
    (h26883 : p616 ∨ p595)
    (h16668 : (¬ p616) ∨ (¬ p1015) ∨ (¬ p1395) ∨ (¬ p1548) ∨ (¬ p1674)) : (¬ p1674) ∨ (¬ p1395) ∨ (¬ p1548) ∨ p595 ∨ (¬ p1015) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1674 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1395 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1548 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16668 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u0)

theorem step29132 (p1385 p1389 p1393 p1396 p1397 p1398 p1399 p1400 : Prop)
    (h26932 : (¬ p1385) ∨ (¬ p1393))
    (h8366 : p1389 ∨ p1393 ∨ (¬ p1396) ∨ (¬ p1397) ∨ (¬ p1398) ∨ (¬ p1399) ∨ (¬ p1400)) : (¬ p1399) ∨ (¬ p1400) ∨ (¬ p1385) ∨ (¬ p1397) ∨ p1389 ∨ (¬ p1396) ∨ (¬ p1398) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1399 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1400 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1397 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1389) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1396 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1398 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p1393) := by
    rcases h26932 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h8366 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u1)

theorem step29134 (p224 p344 p346 p1286 p1545 : Prop)
    (h26863 : p346 ∨ p344)
    (h17543 : (¬ p224) ∨ (¬ p346) ∨ (¬ p1286) ∨ (¬ p1545)) : (¬ p1286) ∨ (¬ p1545) ∨ p344 ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17543 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)

theorem step29135 (p382 p495 p499 p582 p614 p1286 p1392 : Prop)
    (h26875 : p499 ∨ p495)
    (h18685 : (¬ p382) ∨ (¬ p499) ∨ (¬ p582) ∨ (¬ p614) ∨ (¬ p1286) ∨ (¬ p1392)) : (¬ p1286) ∨ p495 ∨ (¬ p614) ∨ (¬ p582) ∨ (¬ p1392) ∨ (¬ p382) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p614 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1392 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18685 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u4)

theorem step29137 (p303 p350 p600 p633 p636 p1286 : Prop)
    (h26885 : p636 ∨ p633)
    (h17003 : (¬ p303) ∨ (¬ p350) ∨ (¬ p600) ∨ (¬ p636) ∨ (¬ p1286)) : (¬ p1286) ∨ p633 ∨ (¬ p303) ∨ (¬ p350) ∨ (¬ p600) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p633) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p600 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17003 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)

theorem step29138 (p350 p367 p382 p600 p633 p636 p1286 : Prop)
    (h26885 : p636 ∨ p633)
    (h17286 : (¬ p350) ∨ (¬ p367) ∨ (¬ p382) ∨ (¬ p600) ∨ (¬ p636) ∨ (¬ p1286)) : (¬ p1286) ∨ p633 ∨ (¬ p350) ∨ (¬ p600) ∨ (¬ p367) ∨ (¬ p382) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p633) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p600 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p367 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17286 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u0)

theorem step29139 (p16 p121 p134 p189 p389 p595 p1206 p1286 : Prop)
    (h26923 : p1206 ∨ p121)
    (h19990 : (¬ p16) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p389) ∨ (¬ p595) ∨ (¬ p1206) ∨ (¬ p1286)) : p121 ∨ (¬ p389) ∨ (¬ p134) ∨ (¬ p16) ∨ (¬ p595) ∨ (¬ p189) ∨ (¬ p1286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19990 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u6)

theorem step29140 (p6 p41 p45 p192 p595 p1286 p1325 p1333 p1454 p1666 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26831 : p45 ∨ p41)
    (h20002 : (¬ p6) ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p595) ∨ (¬ p1286) ∨ (¬ p1333) ∨ (¬ p1454) ∨ (¬ p1666)) : (¬ p1666) ∨ (¬ p1454) ∨ p1325 ∨ p41 ∨ (¬ p1286) ∨ (¬ p595) ∨ (¬ p6) ∨ (¬ p192) := by
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
  have u2 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
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
  have u7 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20002 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u0)

theorem step29142 (p595 p616 p836 p840 p899 p925 p1096 : Prop)
    (h26883 : p616 ∨ p595)
    (h26895 : p840 ∨ p836)
    (h17809 : (¬ p616) ∨ (¬ p840) ∨ (¬ p899) ∨ (¬ p925) ∨ (¬ p1096)) : (¬ p1096) ∨ p595 ∨ p836 ∨ (¬ p899) ∨ (¬ p925) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p595) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p899 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p925 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17809 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u0)

theorem step29143 (p344 p595 p616 p638 p899 p1096 : Prop)
    (h26883 : p616 ∨ p595)
    (h16665 : (¬ p344) ∨ (¬ p616) ∨ (¬ p638) ∨ (¬ p899) ∨ (¬ p1096)) : (¬ p638) ∨ (¬ p899) ∨ (¬ p344) ∨ p595 ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p638 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p899 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16665 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)

theorem step29144 (p225 p544 p595 p616 p882 p899 p1096 : Prop)
    (h26877 : p544 ∨ p225)
    (h26883 : p616 ∨ p595)
    (h16686 : (¬ p544) ∨ (¬ p616) ∨ (¬ p882) ∨ (¬ p899) ∨ (¬ p1096)) : (¬ p899) ∨ (¬ p1096) ∨ (¬ p882) ∨ p225 ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p899 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p882 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16686 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)

theorem step29146 (p161 p382 p406 p622 p1288 p1325 p1333 : Prop)
    (h26869 : p406 ∨ p382)
    (h26931 : p1333 ∨ p1325)
    (h19987 : (¬ p161) ∨ (¬ p406) ∨ (¬ p622) ∨ (¬ p1288) ∨ (¬ p1333)) : (¬ p622) ∨ p382 ∨ p1325 ∨ (¬ p1288) ∨ (¬ p161) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p622 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19987 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)

theorem step29155 (p431 p595 p616 p1229 p1292 p1545 : Prop)
    (h26883 : p616 ∨ p595)
    (h16669 : (¬ p431) ∨ (¬ p616) ∨ (¬ p1229) ∨ (¬ p1292) ∨ (¬ p1545)) : (¬ p1545) ∨ (¬ p1229) ∨ (¬ p1292) ∨ (¬ p431) ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1292 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16669 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u0)

theorem step29156 (p224 p595 p616 p906 p1229 p1292 : Prop)
    (h26883 : p616 ∨ p595)
    (h16563 : (¬ p224) ∨ (¬ p616) ∨ (¬ p906) ∨ (¬ p1229) ∨ (¬ p1292)) : (¬ p906) ∨ (¬ p1229) ∨ (¬ p1292) ∨ p595 ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p906 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1292 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16563 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)

theorem step29158 (p595 p616 p619 : Prop)
    (h26882 : (¬ p595) ∨ (¬ p616))
    (h20790 : p619 ∨ p616) : p619 ∨ (¬ p595) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p619) := fun hu => hn (Or.inl hu)
  have u1 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p616) := by
    rcases h26882 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h20790 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step29174 (p63 p85 p1095 p1096 p1115 : Prop)
    (h26835 : p85 ∨ p63)
    (h16556 : (¬ p85) ∨ (¬ p1095) ∨ (¬ p1096) ∨ (¬ p1115)) : (¬ p1096) ∨ (¬ p1115) ∨ (¬ p1095) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16556 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)

theorem step29175 (p63 p85 p980 p983 p1095 p1096 : Prop)
    (h26903 : p983 ∨ p980)
    (h26835 : p85 ∨ p63)
    (h16629 : (¬ p85) ∨ (¬ p983) ∨ (¬ p1095) ∨ (¬ p1096)) : (¬ p1096) ∨ p980 ∨ (¬ p1095) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16629 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)

theorem step29176 (p15 p69 p1076 p1095 p1096 : Prop)
    (h26833 : p69 ∨ p15)
    (h21019 : (¬ p69) ∨ (¬ p1095) ∨ (¬ p1076) ∨ (¬ p1096)) : (¬ p1095) ∨ (¬ p1076) ∨ p15 ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h21019 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)

theorem step29177 (p63 p85 p1076 p1095 p1096 : Prop)
    (h26835 : p85 ∨ p63)
    (h16445 : (¬ p85) ∨ (¬ p1076) ∨ (¬ p1095) ∨ (¬ p1096)) : (¬ p1096) ∨ p63 ∨ (¬ p1076) ∨ (¬ p1095) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p63) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16445 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)

theorem step29178 (p12 p880 p1036 p1095 : Prop)
    (h26907 : p1036 ∨ p12)
    (h10694 : (¬ p880) ∨ (¬ p1036) ∨ (¬ p1095)) : (¬ p1095) ∨ p12 ∨ (¬ p880) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p880 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h10694 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)

theorem step29179 (p12 p63 p85 p1036 p1095 p1096 : Prop)
    (h26835 : p85 ∨ p63)
    (h26907 : p1036 ∨ p12)
    (h16365 : (¬ p85) ∨ (¬ p1036) ∨ (¬ p1095) ∨ (¬ p1096)) : (¬ p1096) ∨ p63 ∨ (¬ p1095) ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p63) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16365 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)

theorem step29180 (p12 p225 p544 p1036 p1095 p1096 : Prop)
    (h26907 : p1036 ∨ p12)
    (h26877 : p544 ∨ p225)
    (h19162 : (¬ p544) ∨ (¬ p1036) ∨ (¬ p1095) ∨ (¬ p1096)) : p12 ∨ (¬ p1095) ∨ p225 ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p12) := fun hu => hn (Or.inl hu)
  have u1 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19162 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)

theorem step29181 (p595 p616 p668 p899 p1095 p1096 : Prop)
    (h26883 : p616 ∨ p595)
    (h16737 : (¬ p616) ∨ (¬ p668) ∨ (¬ p899) ∨ (¬ p1095) ∨ (¬ p1096)) : (¬ p1096) ∨ (¬ p899) ∨ (¬ p668) ∨ (¬ p1095) ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p899 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16737 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u0)

theorem step29183 (p5 p10 p13 p121 p125 p206 p323 p1095 p1096 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26861 : p323 ∨ p10)
    (h18346 : (¬ p5) ∨ (¬ p13) ∨ (¬ p125) ∨ (¬ p206) ∨ (¬ p323) ∨ (¬ p1095) ∨ (¬ p1096) ∨ (¬ p1206)) : p121 ∨ (¬ p13) ∨ (¬ p206) ∨ p10 ∨ (¬ p1095) ∨ (¬ p5) ∨ (¬ p1096) ∨ (¬ p125) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18346 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u8)

theorem step29184 (p8 p303 p347 p666 p710 p1095 p1102 : Prop)
    (h26889 : p710 ∨ p8)
    (h17494 : (¬ p303) ∨ (¬ p347) ∨ (¬ p666) ∨ (¬ p710) ∨ (¬ p1095) ∨ (¬ p1102)) : (¬ p1095) ∨ p8 ∨ (¬ p1102) ∨ (¬ p666) ∨ (¬ p303) ∨ (¬ p347) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p8) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p666 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17494 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u2)

theorem step29185 (p3 p12 p64 p226 p897 p1036 p1095 : Prop)
    (h26847 : p226 ∨ p3)
    (h26907 : p1036 ∨ p12)
    (h19688 : (¬ p64) ∨ (¬ p226) ∨ (¬ p897) ∨ (¬ p1036) ∨ (¬ p1095)) : p3 ∨ (¬ p1095) ∨ (¬ p897) ∨ p12 ∨ (¬ p64) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19688 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)

theorem step29186 (p980 p983 p1056 p1095 p1101 p1226 : Prop)
    (h26903 : p983 ∨ p980)
    (h17104 : (¬ p983) ∨ (¬ p1056) ∨ (¬ p1095) ∨ (¬ p1101) ∨ (¬ p1226)) : (¬ p1101) ∨ p980 ∨ (¬ p1056) ∨ (¬ p1226) ∨ (¬ p1095) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1056 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17104 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u3)

theorem step29187 (p5 p6 p980 p983 p1095 p1096 p1454 p1666 : Prop)
    (h26903 : p983 ∨ p980)
    (h18951 : (¬ p5) ∨ (¬ p6) ∨ (¬ p983) ∨ (¬ p1095) ∨ (¬ p1096) ∨ (¬ p1454) ∨ (¬ p1666)) : (¬ p1666) ∨ (¬ p1454) ∨ (¬ p5) ∨ (¬ p1096) ∨ p980 ∨ (¬ p6) ∨ (¬ p1095) := by
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
  have u2 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18951 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u0)

theorem step29188 (p16 p189 p419 p424 p665 p796 p1095 p1096 : Prop)
    (h26891 : p796 ∨ p424)
    (h18489 : (¬ p16) ∨ (¬ p189) ∨ (¬ p419) ∨ (¬ p665) ∨ (¬ p796) ∨ (¬ p1095) ∨ (¬ p1096)) : p424 ∨ (¬ p1095) ∨ (¬ p665) ∨ (¬ p1096) ∨ (¬ p16) ∨ (¬ p189) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h18489 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u3)

theorem step29189 (p16 p790 p814 p980 p983 p1015 p1095 p1096 p1335 : Prop)
    (h26903 : p983 ∨ p980)
    (h26893 : p814 ∨ p790)
    (h19195 : (¬ p16) ∨ (¬ p814) ∨ (¬ p983) ∨ (¬ p1015) ∨ (¬ p1095) ∨ (¬ p1096) ∨ (¬ p1335)) : (¬ p1096) ∨ p980 ∨ (¬ p16) ∨ (¬ p1335) ∨ p790 ∨ (¬ p1015) ∨ (¬ p1095) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19195 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u3)

theorem step29190 (p3 p72 p789 p858 p880 p1022 p1076 p1095 p1188 p1545 : Prop)
    (h26897 : p858 ∨ p789)
    (h17880 : (¬ p3) ∨ (¬ p72) ∨ (¬ p858) ∨ (¬ p880) ∨ (¬ p1022) ∨ (¬ p1076) ∨ (¬ p1095) ∨ (¬ p1188) ∨ (¬ p1545)) : (¬ p1022) ∨ (¬ p1188) ∨ p789 ∨ (¬ p1545) ∨ (¬ p880) ∨ (¬ p3) ∨ (¬ p72) ∨ (¬ p1095) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p880 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17880 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u3)

theorem step29192 (p308 p455 p633 p636 p897 p961 p1055 p1095 : Prop)
    (h26885 : p636 ∨ p633)
    (h20247 : (¬ p308) ∨ (¬ p455) ∨ (¬ p636) ∨ (¬ p897) ∨ (¬ p961) ∨ (¬ p1055) ∨ (¬ p1095)) : (¬ p961) ∨ (¬ p1055) ∨ (¬ p1095) ∨ (¬ p455) ∨ (¬ p308) ∨ (¬ p897) ∨ p633 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p308 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p633) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20247 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u2)

theorem step29193 (p16 p163 p167 p189 p225 p668 p1095 p1096 : Prop)
    (h26843 : p167 ∨ p163)
    (h19001 : (¬ p16) ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p225) ∨ (¬ p668) ∨ (¬ p1095) ∨ (¬ p1096)) : p163 ∨ (¬ p225) ∨ (¬ p1096) ∨ (¬ p189) ∨ (¬ p16) ∨ (¬ p668) ∨ (¬ p1095) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p163) := fun hu => hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19001 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u2)

theorem step29195 (p63 p85 p124 p304 p344 p346 p425 p582 p668 p1095 p1096 : Prop)
    (h26859 : p304 ∨ p124)
    (h26863 : p346 ∨ p344)
    (h26835 : p85 ∨ p63)
    (h16779 : (¬ p85) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p425) ∨ (¬ p582) ∨ (¬ p668) ∨ (¬ p1095) ∨ (¬ p1096)) : p124 ∨ (¬ p425) ∨ (¬ p1095) ∨ (¬ p668) ∨ p344 ∨ (¬ p1096) ∨ (¬ p582) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h16779 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u5)

theorem step29196 (p38 p49 p63 p85 p124 p206 p304 p344 p346 p668 p1095 p1096 : Prop)
    (h26859 : p304 ∨ p124)
    (h26835 : p85 ∨ p63)
    (h26863 : p346 ∨ p344)
    (h16656 : (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p206) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p668) ∨ (¬ p1095) ∨ (¬ p1096)) : p124 ∨ (¬ p1096) ∨ (¬ p668) ∨ (¬ p1095) ∨ (¬ p38) ∨ (¬ p206) ∨ p63 ∨ p344 ∨ (¬ p49) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h16656 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u3)
  · exact False.elim (q8 u1)

theorem step29197 (p110 p225 p309 p544 p897 p1055 p1095 : Prop)
    (h26877 : p544 ∨ p225)
    (h17524 : (¬ p110) ∨ (¬ p309) ∨ (¬ p544) ∨ (¬ p897) ∨ (¬ p1055) ∨ (¬ p1095)) : (¬ p110) ∨ p225 ∨ (¬ p897) ∨ (¬ p1055) ∨ (¬ p309) ∨ (¬ p1095) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17524 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)

theorem step29198 (p897 p980 p983 p1095 p1325 : Prop)
    (h26903 : p983 ∨ p980)
    (h17530 : (¬ p897) ∨ (¬ p983) ∨ (¬ p1095) ∨ (¬ p1325)) : p980 ∨ (¬ p897) ∨ (¬ p1095) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : p897 := by
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
  have u4 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17530 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)

theorem step29200 (p5 p13 p1095 p1096 p1140 p1159 p1452 p1465 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h19712 : (¬ p5) ∨ (¬ p13) ∨ (¬ p1095) ∨ (¬ p1096) ∨ (¬ p1159) ∨ (¬ p1452) ∨ (¬ p1465)) : (¬ p1452) ∨ (¬ p1096) ∨ (¬ p1095) ∨ (¬ p5) ∨ (¬ p1465) ∨ p1140 ∨ (¬ p13) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19712 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u4)

theorem step29202 (p124 p304 p497 p640 p1076 p1095 : Prop)
    (h26859 : p304 ∨ p124)
    (h16241 : (¬ p304) ∨ (¬ p497) ∨ (¬ p640) ∨ (¬ p1076) ∨ (¬ p1095)) : (¬ p497) ∨ p124 ∨ (¬ p640) ∨ (¬ p1076) ∨ (¬ p1095) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p497 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p640 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16241 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)

theorem step29203 (p5 p665 p1095 p1096 p1140 p1159 p1325 p1333 p1465 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26931 : p1333 ∨ p1325)
    (h19890 : (¬ p5) ∨ (¬ p665) ∨ (¬ p1095) ∨ (¬ p1096) ∨ (¬ p1159) ∨ (¬ p1333) ∨ (¬ p1465)) : p1140 ∨ p1325 ∨ (¬ p1465) ∨ (¬ p1096) ∨ (¬ p1095) ∨ (¬ p5) ∨ (¬ p665) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19890 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u2)

theorem step29204 (p41 p45 p171 p927 p1095 p1115 : Prop)
    (h26831 : p45 ∨ p41)
    (h16244 : (¬ p45) ∨ (¬ p171) ∨ (¬ p927) ∨ (¬ p1095) ∨ (¬ p1115)) : (¬ p171) ∨ (¬ p1095) ∨ (¬ p1115) ∨ (¬ p927) ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p171 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p927 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16244 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)

theorem step29205 (p3 p72 p234 p665 p880 p997 p1095 p1187 p1325 p1333 p1465 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26921 : p1187 ∨ p234)
    (h19189 : (¬ p3) ∨ (¬ p72) ∨ (¬ p665) ∨ (¬ p880) ∨ (¬ p997) ∨ (¬ p1095) ∨ (¬ p1187) ∨ (¬ p1333) ∨ (¬ p1465)) : (¬ p880) ∨ p1325 ∨ (¬ p1465) ∨ (¬ p72) ∨ p234 ∨ (¬ p3) ∨ (¬ p665) ∨ (¬ p997) ∨ (¬ p1095) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p880 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p234) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p997 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19189 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u2)

theorem step29206 (p728 p834 p897 p904 p917 p1015 : Prop)
    (h26899 : p904 ∨ p897)
    (h19698 : (¬ p728) ∨ (¬ p834) ∨ (¬ p904) ∨ (¬ p917) ∨ (¬ p1015)) : (¬ p728) ∨ p897 ∨ (¬ p834) ∨ (¬ p1015) ∨ (¬ p917) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p897) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p834 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p917 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19698 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)

theorem step29207 (p917 p1096 p1099 p1115 p1229 p1310 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h16529 : (¬ p917) ∨ (¬ p1099) ∨ (¬ p1115) ∨ (¬ p1229) ∨ (¬ p1310)) : (¬ p1229) ∨ (¬ p1115) ∨ (¬ p917) ∨ p1096 ∨ (¬ p1310) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p917 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16529 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)

theorem step29209 (p666 p980 p983 p1325 p1333 : Prop)
    (h26902 : (¬ p980) ∨ (¬ p983))
    (h26931 : p1333 ∨ p1325)
    (h15453 : (¬ p666) ∨ p983 ∨ (¬ p1333)) : (¬ p980) ∨ (¬ p666) ∨ p1325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p666 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : (¬ p983) := by
    rcases h26902 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u4 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h15453 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)

theorem step29210 (p980 p983 p1079 p1452 : Prop)
    (h26902 : (¬ p980) ∨ (¬ p983))
    (h15105 : p983 ∨ (¬ p1079) ∨ (¬ p1452)) : (¬ p1452) ∨ (¬ p980) ∨ (¬ p1079) := by
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
  have u2 : p1079 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p983) := by
    rcases h26902 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h15105 with q0 | q1 | q2
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)

theorem step29211 (p836 p980 p983 p1115 p1116 p1325 : Prop)
    (h26903 : p983 ∨ p980)
    (h26915 : p1116 ∨ p1115)
    (h20463 : (¬ p836) ∨ (¬ p983) ∨ (¬ p1116) ∨ (¬ p1325)) : p980 ∨ (¬ p836) ∨ p1115 ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20463 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)

theorem step29212 (p255 p1076 p1115 p1116 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h12403 : (¬ p255) ∨ (¬ p1076) ∨ (¬ p1116)) : (¬ p255) ∨ p1115 ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p255 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1115) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h12403 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)

theorem step29213 (p4 p124 p125 p255 p668 p1115 p1116 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h17348 : (¬ p4) ∨ (¬ p124) ∨ (¬ p125) ∨ (¬ p255) ∨ (¬ p668) ∨ (¬ p1116)) : (¬ p125) ∨ (¬ p255) ∨ (¬ p4) ∨ (¬ p668) ∨ p1115 ∨ (¬ p124) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p255 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17348 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)

theorem step29215 (p185 p189 p237 p1076 p1115 p1116 : Prop)
    (h26851 : p237 ∨ p185)
    (h26915 : p1116 ∨ p1115)
    (h17551 : (¬ p189) ∨ (¬ p237) ∨ (¬ p1076) ∨ (¬ p1116)) : p185 ∨ (¬ p1076) ∨ p1115 ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p185) := fun hu => hn (Or.inl hu)
  have u1 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17551 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)

theorem step29216 (p63 p125 p303 p665 p918 p928 p1115 p1116 : Prop)
    (h26901 : p928 ∨ p918)
    (h26915 : p1116 ∨ p1115)
    (h25873 : (¬ p928) ∨ (¬ p1116) ∨ (¬ p125) ∨ (¬ p63) ∨ (¬ p303) ∨ (¬ p665)) : (¬ p125) ∨ p918 ∨ p1115 ∨ (¬ p665) ∨ (¬ p63) ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h25873 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u3)

theorem step29217 (p344 p918 p928 p1076 p1115 p1116 : Prop)
    (h26901 : p928 ∨ p918)
    (h26915 : p1116 ∨ p1115)
    (h16273 : (¬ p344) ∨ (¬ p928) ∨ (¬ p1076) ∨ (¬ p1116)) : (¬ p344) ∨ p918 ∨ (¬ p1076) ∨ p1115 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16273 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)

theorem step29218 (p101 p185 p237 p1076 p1115 p1116 : Prop)
    (h26851 : p237 ∨ p185)
    (h26915 : p1116 ∨ p1115)
    (h17544 : (¬ p101) ∨ (¬ p237) ∨ (¬ p1076) ∨ (¬ p1116)) : p185 ∨ (¬ p1076) ∨ p1115 ∨ (¬ p101) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p185) := fun hu => hn (Or.inl hu)
  have u1 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17544 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)

theorem step29219 (p86 p185 p237 p303 p420 p495 p665 p1115 p1116 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h26851 : p237 ∨ p185)
    (h17328 : (¬ p86) ∨ (¬ p237) ∨ (¬ p303) ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p665) ∨ (¬ p1116)) : (¬ p420) ∨ (¬ p495) ∨ (¬ p86) ∨ p1115 ∨ p185 ∨ (¬ p665) ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17328 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u7)

theorem step29220 (p10 p13 p121 p125 p185 p237 p267 p323 p1115 p1116 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26851 : p237 ∨ p185)
    (h26861 : p323 ∨ p10)
    (h26915 : p1116 ∨ p1115)
    (h16493 : (¬ p13) ∨ (¬ p125) ∨ (¬ p237) ∨ (¬ p267) ∨ (¬ p323) ∨ (¬ p1116) ∨ (¬ p1206)) : p121 ∨ p185 ∨ p10 ∨ (¬ p125) ∨ (¬ p267) ∨ (¬ p13) ∨ p1115 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p267 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h16493 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u7)

theorem step29221 (p41 p45 p918 p928 p1076 p1115 p1116 : Prop)
    (h26901 : p928 ∨ p918)
    (h26915 : p1116 ∨ p1115)
    (h26831 : p45 ∨ p41)
    (h16245 : (¬ p45) ∨ (¬ p928) ∨ (¬ p1076) ∨ (¬ p1116)) : p918 ∨ (¬ p1076) ∨ p1115 ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p918) := fun hu => hn (Or.inl hu)
  have u1 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16245 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)

theorem step29222 (p12 p166 p1115 p1116 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h11596 : p12 ∨ (¬ p166) ∨ (¬ p1116)) : (¬ p166) ∨ p1115 ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p166 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1115) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p12) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h11596 with q0 | q1 | q2
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)

theorem step29223 (p3 p12 p226 p836 p1036 p1115 p1116 : Prop)
    (h26847 : p226 ∨ p3)
    (h26915 : p1116 ∨ p1115)
    (h26907 : p1036 ∨ p12)
    (h19579 : (¬ p226) ∨ (¬ p836) ∨ (¬ p1036) ∨ (¬ p1116)) : p3 ∨ p1115 ∨ (¬ p836) ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1115) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19579 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)

theorem step29225 (p982 p1115 p1116 p1584 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h12280 : (¬ p982) ∨ (¬ p1116) ∨ (¬ p1584)) : (¬ p1584) ∨ (¬ p982) ∨ p1115 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p982 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h12280 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)

theorem step29226 (p769 p982 p1055 p1061 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h12018 : (¬ p769) ∨ (¬ p982) ∨ (¬ p1061)) : (¬ p769) ∨ (¬ p982) ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p769 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p982 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h12018 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)

theorem step29229 (p160 p161 p925 p1057 p1115 p1116 p1306 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h20365 : (¬ p160) ∨ (¬ p161) ∨ (¬ p925) ∨ (¬ p1057) ∨ (¬ p1116) ∨ (¬ p1306)) : (¬ p160) ∨ (¬ p1057) ∨ (¬ p161) ∨ (¬ p1306) ∨ (¬ p925) ∨ p1115 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1057 := by
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
  have u4 : p925 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20365 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)

theorem step29234 (p8 p667 p1055 p1061 : Prop)
    (h26908 : (¬ p1055) ∨ (¬ p1061))
    (h6746 : (¬ p8) ∨ (¬ p667) ∨ p1061) : (¬ p1055) ∨ (¬ p667) ∨ (¬ p8) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p667 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1061) := by
    rcases h26908 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h6746 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (u3 q2)

theorem step29235 (p12 p225 p544 p667 p1036 : Prop)
    (h26907 : p1036 ∨ p12)
    (h26877 : p544 ∨ p225)
    (h9327 : (¬ p544) ∨ (¬ p667) ∨ (¬ p1036)) : p12 ∨ (¬ p667) ∨ p225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p12) := fun hu => hn (Or.inl hu)
  have u1 : p667 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p225) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h9327 with q0 | q1 | q2
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)

theorem step29237 (p667 p836 p840 p1115 p1116 : Prop)
    (h26914 : (¬ p1115) ∨ (¬ p1116))
    (h26895 : p840 ∨ p836)
    (h11583 : (¬ p667) ∨ (¬ p840) ∨ p1116) : (¬ p1115) ∨ (¬ p667) ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p667 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1116) := by
    rcases h26914 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u4 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h11583 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (u3 q2)

theorem step29238 (p667 p836 p840 p1115 : Prop)
    (h26895 : p840 ∨ p836)
    (h11589 : (¬ p667) ∨ (¬ p840) ∨ (¬ p1115)) : (¬ p1115) ∨ (¬ p667) ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p667 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h11589 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)

theorem step29239 (p667 p901 p980 p983 p1287 p1325 : Prop)
    (h26903 : p983 ∨ p980)
    (h17928 : (¬ p667) ∨ (¬ p901) ∨ (¬ p983) ∨ (¬ p1287) ∨ (¬ p1325)) : p980 ∨ (¬ p901) ∨ (¬ p1287) ∨ (¬ p667) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : p901 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p667 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17928 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u4)

theorem step29242 (p667 p897 p904 p1095 : Prop)
    (h26899 : p904 ∨ p897)
    (h15614 : (¬ p667) ∨ (¬ p904) ∨ p1095) : (¬ p667) ∨ p1095 ∨ p897 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p667 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1095) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p897) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h15614 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (u1 q2)

theorem step29243 (p12 p225 p544 p667 : Prop)
    (h26877 : p544 ∨ p225)
    (h14887 : p12 ∨ (¬ p544) ∨ (¬ p667)) : p12 ∨ (¬ p667) ∨ p225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p12) := fun hu => hn (Or.inl hu)
  have u1 : p667 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p225) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h14887 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)

theorem step29244 (p189 p422 p667 p980 p983 p1465 : Prop)
    (h26903 : p983 ∨ p980)
    (h18983 : (¬ p189) ∨ (¬ p422) ∨ (¬ p667) ∨ (¬ p983) ∨ (¬ p1465)) : (¬ p422) ∨ p980 ∨ (¬ p189) ∨ (¬ p667) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p667 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18983 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)

theorem step29245 (p419 p542 p667 p980 p983 p1325 : Prop)
    (h26903 : p983 ∨ p980)
    (h16794 : (¬ p419) ∨ (¬ p542) ∨ (¬ p667) ∨ (¬ p983) ∨ (¬ p1325)) : p980 ∨ (¬ p542) ∨ (¬ p1325) ∨ (¬ p419) ∨ (¬ p667) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p667 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h16794 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)

theorem step29271 (p12 p165 p189 p534 p667 p1036 p1584 : Prop)
    (h26907 : p1036 ∨ p12)
    (h17936 : (¬ p165) ∨ (¬ p189) ∨ (¬ p534) ∨ (¬ p667) ∨ (¬ p1036) ∨ (¬ p1584)) : (¬ p534) ∨ (¬ p165) ∨ (¬ p1584) ∨ (¬ p189) ∨ (¬ p667) ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p165 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p667 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17936 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)

theorem step29273 (p15 p18 p69 p121 p344 p389 p667 p980 p983 p1206 p1325 : Prop)
    (h26903 : p983 ∨ p980)
    (h26923 : p1206 ∨ p121)
    (h26833 : p69 ∨ p15)
    (h20315 : (¬ p18) ∨ (¬ p69) ∨ (¬ p344) ∨ (¬ p389) ∨ (¬ p667) ∨ (¬ p983) ∨ (¬ p1206) ∨ (¬ p1325)) : p980 ∨ (¬ p18) ∨ (¬ p1325) ∨ (¬ p344) ∨ p121 ∨ (¬ p667) ∨ (¬ p389) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p121) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p667 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h20315 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u2)

theorem step29275 (p980 p1074 p1096 p1099 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26913 : p1099 ∨ p1096)
    (h16310 : (¬ p980) ∨ (¬ p1074) ∨ (¬ p1099) ∨ (¬ p1333)) : (¬ p980) ∨ p1325 ∨ (¬ p1074) ∨ p1096 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16310 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step29276 (p666 p980 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h11635 : (¬ p666) ∨ (¬ p980) ∨ (¬ p1333)) : (¬ p980) ∨ (¬ p666) ∨ p1325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p666 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h11635 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)

theorem step29278 (p8 p980 p1055 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h19315 : (¬ p8) ∨ (¬ p980) ∨ (¬ p1055) ∨ (¬ p1333)) : (¬ p1055) ∨ (¬ p8) ∨ p1325 ∨ (¬ p980) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19315 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)

theorem step29279 (p185 p980 p1115 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h19065 : (¬ p185) ∨ (¬ p980) ∨ (¬ p1115) ∨ (¬ p1333)) : (¬ p1115) ∨ (¬ p980) ∨ p1325 ∨ (¬ p185) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19065 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)

theorem step29280 (p125 p161 p303 p665 p980 p1096 p1225 p1311 : Prop)
    (h26925 : p1225 ∨ p161)
    (h25899 : (¬ p980) ∨ (¬ p1311) ∨ (¬ p1096) ∨ (¬ p303) ∨ (¬ p665) ∨ (¬ p125) ∨ (¬ p1225)) : p161 ∨ (¬ p125) ∨ (¬ p1311) ∨ (¬ p980) ∨ (¬ p1096) ∨ (¬ p665) ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p161) := fun hu => hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1311 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
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
  have u6 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h25899 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step29281 (p16 p185 p495 p499 p980 p1115 p1449 p1611 : Prop)
    (h26875 : p499 ∨ p495)
    (h19914 : (¬ p16) ∨ (¬ p185) ∨ (¬ p499) ∨ (¬ p980) ∨ (¬ p1115) ∨ (¬ p1449) ∨ (¬ p1611)) : (¬ p1115) ∨ (¬ p1611) ∨ (¬ p1449) ∨ p495 ∨ (¬ p185) ∨ (¬ p980) ∨ (¬ p16) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1611 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1449 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p980 := by
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
  rcases h19914 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u1)

theorem step29282 (p6 p127 p185 p190 p980 p1115 p1449 p1665 : Prop)
    (h26839 : p127 ∨ p6)
    (h19040 : (¬ p127) ∨ (¬ p185) ∨ (¬ p190) ∨ (¬ p980) ∨ (¬ p1115) ∨ (¬ p1449) ∨ (¬ p1665)) : (¬ p1665) ∨ (¬ p1449) ∨ (¬ p980) ∨ p6 ∨ (¬ p1115) ∨ (¬ p190) ∨ (¬ p185) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1449 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19040 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u0)

theorem step29283 (p125 p185 p263 p362 p434 p980 p1115 p1330 : Prop)
    (h26865 : p362 ∨ p125)
    (h19481 : (¬ p185) ∨ (¬ p263) ∨ (¬ p362) ∨ (¬ p434) ∨ (¬ p980) ∨ (¬ p1115) ∨ (¬ p1330)) : (¬ p434) ∨ (¬ p1115) ∨ (¬ p263) ∨ (¬ p980) ∨ p125 ∨ (¬ p185) ∨ (¬ p1330) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p263 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19481 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u6)

theorem step29286 (p2 p124 p190 p261 p286 p304 p481 p980 p1115 p1330 p1366 : Prop)
    (h26859 : p304 ∨ p124)
    (h26873 : p481 ∨ p2)
    (h20460 : (¬ p190) ∨ (¬ p261) ∨ (¬ p286) ∨ (¬ p304) ∨ (¬ p481) ∨ (¬ p980) ∨ (¬ p1115) ∨ (¬ p1330) ∨ (¬ p1366)) : (¬ p1366) ∨ p124 ∨ (¬ p190) ∨ p2 ∨ (¬ p1115) ∨ (¬ p286) ∨ (¬ p1330) ∨ (¬ p261) ∨ (¬ p980) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20460 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u0)

theorem step29287 (p12 p163 p167 p189 p980 p1036 : Prop)
    (h26907 : p1036 ∨ p12)
    (h26843 : p167 ∨ p163)
    (h17927 : (¬ p167) ∨ (¬ p189) ∨ (¬ p980) ∨ (¬ p1036)) : p12 ∨ p163 ∨ (¬ p980) ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p12) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17927 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step29288 (p3 p12 p17 p194 p226 p256 p980 p1036 p1449 p1651 : Prop)
    (h26907 : p1036 ∨ p12)
    (h26847 : p226 ∨ p3)
    (h26853 : p256 ∨ p17)
    (h18998 : (¬ p194) ∨ (¬ p226) ∨ (¬ p256) ∨ (¬ p980) ∨ (¬ p1036) ∨ (¬ p1449) ∨ (¬ p1651)) : (¬ p1651) ∨ (¬ p194) ∨ (¬ p980) ∨ p12 ∨ p3 ∨ (¬ p1449) ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1651 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1449 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18998 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u0)

theorem step29289 (p3 p12 p194 p226 p790 p980 p1022 p1036 p1330 : Prop)
    (h26847 : p226 ∨ p3)
    (h26907 : p1036 ∨ p12)
    (h19685 : (¬ p194) ∨ (¬ p226) ∨ (¬ p790) ∨ (¬ p980) ∨ (¬ p1022) ∨ (¬ p1036) ∨ (¬ p1330)) : (¬ p1022) ∨ p3 ∨ (¬ p194) ∨ p12 ∨ (¬ p980) ∨ (¬ p1330) ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19685 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u5)

theorem step29290 (p63 p85 p918 p980 p1115 : Prop)
    (h26835 : p85 ∨ p63)
    (h16573 : (¬ p85) ∨ (¬ p918) ∨ (¬ p980) ∨ (¬ p1115)) : (¬ p1115) ∨ (¬ p918) ∨ p63 ∨ (¬ p980) := by
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
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16573 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)

theorem step29291 (p88 p101 p102 p185 p577 p980 p1115 p1611 p1666 : Prop)
    (h26837 : p102 ∨ p101)
    (h19039 : (¬ p88) ∨ (¬ p102) ∨ (¬ p185) ∨ (¬ p577) ∨ (¬ p980) ∨ (¬ p1115) ∨ (¬ p1611) ∨ (¬ p1666)) : (¬ p1611) ∨ (¬ p1666) ∨ (¬ p1115) ∨ (¬ p185) ∨ p101 ∨ (¬ p88) ∨ (¬ p980) ∨ (¬ p577) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1611 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1666 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19039 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u1)

theorem step29292 (p11 p17 p256 p662 p980 p1443 p1452 : Prop)
    (h26935 : p1443 ∨ p11)
    (h26853 : p256 ∨ p17)
    (h17407 : (¬ p256) ∨ (¬ p662) ∨ (¬ p980) ∨ (¬ p1443) ∨ (¬ p1452)) : (¬ p1452) ∨ (¬ p980) ∨ p11 ∨ (¬ p662) ∨ p17 := by
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
  have u2 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p662 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17407 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)

theorem step29293 (p6 p121 p127 p980 p1452 : Prop)
    (h26839 : p127 ∨ p6)
    (h19621 : (¬ p121) ∨ (¬ p127) ∨ (¬ p980) ∨ (¬ p1452)) : (¬ p1452) ∨ (¬ p121) ∨ p6 ∨ (¬ p980) := by
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
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19621 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)

theorem step29299 (p14 p18 p19 p108 : Prop)
    (h26829 : p19 ∨ p18)
    (h14142 : p14 ∨ (¬ p19) ∨ (¬ p108)) : p14 ∨ (¬ p108) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h14142 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)

theorem step29300 (p12 p1036 p1041 : Prop)
    (h26906 : (¬ p12) ∨ (¬ p1036))
    (h20717 : p1036 ∨ p1041) : (¬ p12) ∨ p1041 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1041) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p1036) := by
    rcases h26906 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h20717 with q0 | q1
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)

theorem step29301 (p12 p169 p1036 p1115 : Prop)
    (h26906 : (¬ p12) ∨ (¬ p1036))
    (h15764 : (¬ p169) ∨ p1036 ∨ (¬ p1115)) : (¬ p12) ∨ (¬ p1115) ∨ (¬ p169) := by
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
  have u2 : p169 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1036) := by
    rcases h26906 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h15764 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u1)

theorem step29302 (p12 p104 p1036 p1076 : Prop)
    (h26906 : (¬ p12) ∨ (¬ p1036))
    (h14910 : (¬ p104) ∨ p1036 ∨ (¬ p1076)) : (¬ p104) ∨ (¬ p12) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p104 := by
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
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1036) := by
    rcases h26906 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h14910 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u2)

theorem step29318 (p18 p19 p258 p288 p1644 p1665 : Prop)
    (h26829 : p19 ∨ p18)
    (h26855 : p288 ∨ p258)
    (h17125 : (¬ p19) ∨ (¬ p288) ∨ (¬ p1644) ∨ (¬ p1665)) : (¬ p1665) ∨ (¬ p1644) ∨ p18 ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1644 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17125 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)

theorem step29319 (p18 p19 p67 p206 p1624 p1665 : Prop)
    (h26829 : p19 ∨ p18)
    (h18829 : (¬ p19) ∨ (¬ p67) ∨ (¬ p206) ∨ (¬ p1624) ∨ (¬ p1665)) : (¬ p1624) ∨ (¬ p1665) ∨ (¬ p206) ∨ p18 ∨ (¬ p67) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1624 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18829 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)

theorem step29321 (p10 p185 p194 p206 p237 p351 p836 p840 p1624 p1665 : Prop)
    (h26851 : p237 ∨ p185)
    (h26895 : p840 ∨ p836)
    (h20308 : (¬ p10) ∨ (¬ p194) ∨ (¬ p206) ∨ (¬ p237) ∨ (¬ p351) ∨ (¬ p840) ∨ (¬ p1624) ∨ (¬ p1665)) : (¬ p1665) ∨ (¬ p1624) ∨ (¬ p206) ∨ (¬ p194) ∨ (¬ p351) ∨ p185 ∨ p836 ∨ (¬ p10) := by
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
  have u2 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u9 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20308 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u0)

theorem step29322 (p63 p121 p1206 p1606 p1665 p1667 : Prop)
    (h26923 : p1206 ∨ p121)
    (h20015 : (¬ p63) ∨ (¬ p1206) ∨ (¬ p1606) ∨ (¬ p1665) ∨ (¬ p1667)) : (¬ p1667) ∨ (¬ p1606) ∨ (¬ p1665) ∨ (¬ p63) ∨ p121 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1667 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1606 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p121) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20015 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u0)

theorem step29323 (p41 p45 p101 p192 p206 p1624 p1665 : Prop)
    (h26831 : p45 ∨ p41)
    (h18406 : (¬ p45) ∨ (¬ p101) ∨ (¬ p192) ∨ (¬ p206) ∨ (¬ p1624) ∨ (¬ p1665)) : (¬ p1665) ∨ (¬ p1624) ∨ (¬ p192) ∨ (¬ p206) ∨ p41 ∨ (¬ p101) := by
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
  have u2 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18406 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u0)

theorem step29324 (p14 p18 p19 p104 p229 p757 p1665 : Prop)
    (h26849 : p229 ∨ p14)
    (h26829 : p19 ∨ p18)
    (h18005 : (¬ p19) ∨ (¬ p104) ∨ (¬ p229) ∨ (¬ p757) ∨ (¬ p1665)) : (¬ p1665) ∨ (¬ p757) ∨ p14 ∨ (¬ p104) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p757 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18005 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)

theorem step29325 (p124 p134 p210 p224 p304 p344 p346 : Prop)
    (h26859 : p304 ∨ p124)
    (h26863 : p346 ∨ p344)
    (h18422 : (¬ p134) ∨ (¬ p210) ∨ (¬ p224) ∨ (¬ p304) ∨ (¬ p346)) : p124 ∨ (¬ p210) ∨ (¬ p134) ∨ (¬ p224) ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18422 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)

theorem step29326 (p125 p134 p210 p224 p303 p657 : Prop)
    (h26887 : p657 ∨ p224)
    (h18613 : (¬ p125) ∨ (¬ p134) ∨ (¬ p210) ∨ (¬ p303) ∨ (¬ p657)) : (¬ p125) ∨ (¬ p210) ∨ (¬ p303) ∨ (¬ p134) ∨ p224 := by
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
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18613 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step29328 (p2 p18 p72 p125 p210 p224 p351 p419 p481 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h26873 : p481 ∨ p2)
    (h20577 : (¬ p18) ∨ (¬ p72) ∨ (¬ p125) ∨ (¬ p210) ∨ (¬ p224) ∨ (¬ p351) ∨ (¬ p481) ∨ (¬ p996)) : p419 ∨ (¬ p125) ∨ (¬ p224) ∨ p2 ∨ (¬ p72) ∨ (¬ p18) ∨ (¬ p351) ∨ (¬ p210) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20577 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u8)

theorem step29329 (p63 p125 p134 p210 p303 p1022 p1385 p1393 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h25901 : (¬ p125) ∨ (¬ p134) ∨ (¬ p63) ∨ (¬ p303) ∨ (¬ p1393) ∨ (¬ p1022) ∨ (¬ p210)) : (¬ p1022) ∨ p1385 ∨ (¬ p63) ∨ (¬ p210) ∨ (¬ p303) ∨ (¬ p134) ∨ (¬ p125) := by
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
  have u3 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h25901 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u3)

theorem step29330 (p101 p102 p124 p210 : Prop)
    (h26837 : p102 ∨ p101)
    (h11124 : (¬ p102) ∨ p124 ∨ (¬ p210)) : (¬ p210) ∨ p124 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h11124 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u0)

theorem step29332 (p18 p124 p210 p224 p304 p344 p346 : Prop)
    (h26859 : p304 ∨ p124)
    (h26863 : p346 ∨ p344)
    (h20126 : (¬ p18) ∨ (¬ p210) ∨ (¬ p224) ∨ (¬ p304) ∨ (¬ p346)) : (¬ p210) ∨ p124 ∨ (¬ p18) ∨ (¬ p224) ∨ p344 := by
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
  have u3 : p224 := by
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
  rcases h20126 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)

theorem step29334 (p41 p45 p101 p102 p210 p455 p580 p961 : Prop)
    (h26831 : p45 ∨ p41)
    (h26837 : p102 ∨ p101)
    (h18643 : (¬ p45) ∨ (¬ p102) ∨ (¬ p210) ∨ (¬ p455) ∨ (¬ p580) ∨ (¬ p961)) : (¬ p961) ∨ (¬ p210) ∨ p41 ∨ p101 ∨ (¬ p455) ∨ (¬ p580) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p580 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18643 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u0)

theorem step29336 (p8 p134 p210 p305 p434 p710 p734 : Prop)
    (h26889 : p710 ∨ p8)
    (h17059 : (¬ p134) ∨ (¬ p210) ∨ (¬ p305) ∨ (¬ p434) ∨ (¬ p710) ∨ (¬ p734)) : (¬ p434) ∨ (¬ p210) ∨ (¬ p134) ∨ (¬ p734) ∨ (¬ p305) ∨ p8 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17059 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)

theorem step29337 (p124 p134 p210 p304 p422 p1084 p1211 p1256 : Prop)
    (h26929 : p1256 ∨ p422)
    (h26859 : p304 ∨ p124)
    (h16984 : (¬ p134) ∨ (¬ p210) ∨ (¬ p304) ∨ (¬ p1084) ∨ (¬ p1211) ∨ (¬ p1256)) : (¬ p210) ∨ (¬ p1211) ∨ p422 ∨ (¬ p134) ∨ (¬ p1084) ∨ p124 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h16984 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u6)

theorem step29338 (p14 p25 p105 p210 p229 p455 p961 : Prop)
    (h26849 : p229 ∨ p14)
    (h20190 : (¬ p25) ∨ (¬ p105) ∨ (¬ p210) ∨ (¬ p229) ∨ (¬ p455) ∨ (¬ p961)) : (¬ p961) ∨ (¬ p25) ∨ (¬ p455) ∨ p14 ∨ (¬ p210) ∨ (¬ p105) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p25 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20190 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u0)

theorem step29340 (p2 p422 p424 p481 p796 p1001 p1256 p1325 p1333 : Prop)
    (h26891 : p796 ∨ p424)
    (h26931 : p1333 ∨ p1325)
    (h26929 : p1256 ∨ p422)
    (h26873 : p481 ∨ p2)
    (h17293 : (¬ p481) ∨ (¬ p796) ∨ (¬ p1001) ∨ (¬ p1256) ∨ (¬ p1333)) : p424 ∨ p1325 ∨ p422 ∨ (¬ p1001) ∨ p2 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1001 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17293 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u6)

theorem step29343 (p419 p996 p998 p1005 p1006 p1007 p1008 p1009 : Prop)
    (h26904 : (¬ p419) ∨ (¬ p996))
    (h5845 : p996 ∨ p998 ∨ (¬ p1005) ∨ (¬ p1006) ∨ (¬ p1007) ∨ (¬ p1008) ∨ (¬ p1009)) : (¬ p1005) ∨ (¬ p1009) ∨ (¬ p419) ∨ p998 ∨ (¬ p1008) ∨ (¬ p1007) ∨ (¬ p1006) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1005 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1009 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p998) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1008 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1007 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1006 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p996) := by
    rcases h26904 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h5845 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u7 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u1)

theorem step29346 (p595 p616 p1229 p1232 p1293 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h26882 : (¬ p595) ∨ (¬ p616))
    (h10564 : p616 ∨ (¬ p1232) ∨ (¬ p1293)) : (¬ p1293) ∨ p1229 ∨ (¬ p595) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1293 := by
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
  rcases h10564 with q0 | q1 | q2
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)

theorem step29351 (p1229 p1232 p1235 : Prop)
    (h26926 : (¬ p1229) ∨ (¬ p1232))
    (h20675 : p1235 ∨ p1232) : p1235 ∨ (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1235) := fun hu => hn (Or.inl hu)
  have u1 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1232) := by
    rcases h26926 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h20675 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step29354 (p15 p69 p235 p1229 p1232 : Prop)
    (h26833 : p69 ∨ p15)
    (h26926 : (¬ p1229) ∨ (¬ p1232))
    (h13643 : (¬ p69) ∨ (¬ p235) ∨ p1232) : (¬ p235) ∨ p15 ∨ (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p235 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u4 : (¬ p1232) := by
    rcases h26926 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h13643 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (u4 q2)

theorem step29356 (p83 p595 p790 p814 p1391 : Prop)
    (h26893 : p814 ∨ p790)
    (h10647 : (¬ p83) ∨ (¬ p595) ∨ (¬ p814) ∨ (¬ p1391)) : (¬ p1391) ∨ (¬ p83) ∨ p790 ∨ (¬ p595) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1391 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h10647 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step29357 (p576 p581 p789 p790 p1287 p1387 : Prop)
    (h26879 : p581 ∨ p576)
    (h20645 : (¬ p581) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1287) ∨ (¬ p1387)) : (¬ p1387) ∨ (¬ p789) ∨ p576 ∨ (¬ p1287) ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20645 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u0)

theorem step29358 (p63 p303 p789 p1385 p1393 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h17966 : (¬ p63) ∨ (¬ p303) ∨ (¬ p789) ∨ (¬ p1393)) : p1385 ∨ (¬ p303) ∨ (¬ p789) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1385) := fun hu => hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17966 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step29359 (p125 p362 p434 p789 p1015 : Prop)
    (h26865 : p362 ∨ p125)
    (h17226 : (¬ p362) ∨ (¬ p434) ∨ (¬ p789) ∨ (¬ p1015)) : (¬ p1015) ∨ (¬ p434) ∨ (¬ p789) ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17226 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)

theorem step29361 (p6 p101 p194 p344 p346 p687 p789 p820 p1015 : Prop)
    (h26863 : p346 ∨ p344)
    (h19707 : (¬ p6) ∨ (¬ p101) ∨ (¬ p194) ∨ (¬ p346) ∨ (¬ p687) ∨ (¬ p789) ∨ (¬ p820) ∨ (¬ p1015)) : (¬ p101) ∨ p344 ∨ (¬ p820) ∨ (¬ p6) ∨ (¬ p1015) ∨ (¬ p789) ∨ (¬ p687) ∨ (¬ p194) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p820 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19707 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u4)

theorem step29362 (p6 p41 p45 p90 p121 p192 p389 p789 p790 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26831 : p45 ∨ p41)
    (h26586 : p90)
    (h20566 : (¬ p6) ∨ (¬ p45) ∨ (¬ p90) ∨ (¬ p192) ∨ (¬ p389) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1206)) : (¬ p389) ∨ p121 ∨ p41 ∨ (¬ p789) ∨ (¬ p6) ∨ (¬ p790) ∨ (¬ p192) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p121) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p90 := by
    exact h26586
  rcases h20566 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u7)

theorem step29363 (p17 p189 p256 p419 p519 p789 : Prop)
    (h26853 : p256 ∨ p17)
    (h17780 : (¬ p189) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p519) ∨ (¬ p789)) : (¬ p419) ∨ (¬ p789) ∨ (¬ p189) ∨ (¬ p519) ∨ p17 := by
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
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p519 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17780 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)

theorem step29365 (p17 p90 p256 p519 p789 p1287 p1387 : Prop)
    (h26853 : p256 ∨ p17)
    (h26586 : p90)
    (h17965 : (¬ p90) ∨ (¬ p256) ∨ (¬ p519) ∨ (¬ p789) ∨ (¬ p1287) ∨ (¬ p1387)) : (¬ p1387) ∨ (¬ p789) ∨ (¬ p519) ∨ p17 ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p519 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p90 := by
    exact h26586
  rcases h17965 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u0)

theorem step29366 (p3 p12 p41 p45 p90 p192 p226 p789 p790 p1036 : Prop)
    (h26847 : p226 ∨ p3)
    (h26907 : p1036 ∨ p12)
    (h26586 : p90)
    (h26831 : p45 ∨ p41)
    (h25902 : (¬ p1036) ∨ (¬ p45) ∨ (¬ p90) ∨ (¬ p789) ∨ (¬ p226) ∨ (¬ p192) ∨ (¬ p790)) : (¬ p790) ∨ p3 ∨ p12 ∨ (¬ p192) ∨ (¬ p789) ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p90 := by
    exact h26586
  have u9 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h25902 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u0)

theorem step29367 (p125 p362 p384 p521 p789 p961 : Prop)
    (h26865 : p362 ∨ p125)
    (h16880 : (¬ p362) ∨ (¬ p384) ∨ (¬ p521) ∨ (¬ p789) ∨ (¬ p961)) : (¬ p521) ∨ (¬ p789) ∨ p125 ∨ (¬ p961) ∨ (¬ p384) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p521 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p384 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16880 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)

theorem step29369 (p64 p86 p206 p389 p455 p456 p789 p790 p1611 p1624 : Prop)
    (h26871 : p456 ∨ p455)
    (h20314 : (¬ p64) ∨ (¬ p86) ∨ (¬ p206) ∨ (¬ p389) ∨ (¬ p456) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1611) ∨ (¬ p1624)) : (¬ p1611) ∨ (¬ p1624) ∨ (¬ p789) ∨ (¬ p389) ∨ (¬ p790) ∨ (¬ p64) ∨ p455 ∨ (¬ p86) ∨ (¬ p206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1611 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1624 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p455) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20314 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u0)
  · exact False.elim (q8 u1)

theorem step29370 (p15 p49 p84 p389 p455 p456 p495 p789 p790 : Prop)
    (h26871 : p456 ∨ p455)
    (h20320 : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p389) ∨ (¬ p456) ∨ (¬ p495) ∨ (¬ p789) ∨ (¬ p790)) : p455 ∨ (¬ p84) ∨ (¬ p790) ∨ (¬ p49) ∨ (¬ p15) ∨ (¬ p495) ∨ (¬ p389) ∨ (¬ p789) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h20320 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u2)

theorem step29372 (p185 p237 p789 p918 p1385 p1393 : Prop)
    (h26851 : p237 ∨ p185)
    (h26933 : p1393 ∨ p1385)
    (h20568 : (¬ p237) ∨ (¬ p789) ∨ (¬ p918) ∨ (¬ p1393)) : p185 ∨ p1385 ∨ (¬ p918) ∨ (¬ p789) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p185) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1385) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20568 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)

theorem step29373 (p10 p15 p24 p39 p69 p88 p323 p382 p495 p499 p521 p789 p815 : Prop)
    (h26833 : p69 ∨ p15)
    (h26875 : p499 ∨ p495)
    (h26861 : p323 ∨ p10)
    (h19169 : (¬ p24) ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p323) ∨ (¬ p382) ∨ (¬ p499) ∨ (¬ p521) ∨ (¬ p789) ∨ (¬ p815)) : (¬ p24) ∨ p15 ∨ (¬ p521) ∨ (¬ p382) ∨ (¬ p39) ∨ (¬ p789) ∨ (¬ p88) ∨ p495 ∨ (¬ p815) ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p521 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p815 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u11 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u12 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h19169 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u12)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u11)
  · exact False.elim (q7 u2)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u8)

theorem step29374 (p83 p1273 p1325 p1333 p1349 p1510 p1772 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h19269 : (¬ p83) ∨ (¬ p1273) ∨ (¬ p1333) ∨ (¬ p1349) ∨ (¬ p1510) ∨ (¬ p1772)) : (¬ p1510) ∨ (¬ p1772) ∨ p1325 ∨ (¬ p1273) ∨ (¬ p1349) ∨ (¬ p83) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1510 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1772 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19269 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u1)

theorem step29375 (p5 p6 p63 p121 p532 p1206 p1512 p1771 : Prop)
    (h26923 : p1206 ∨ p121)
    (h19716 : (¬ p5) ∨ (¬ p6) ∨ (¬ p63) ∨ (¬ p532) ∨ (¬ p1206) ∨ (¬ p1512) ∨ (¬ p1771)) : (¬ p1771) ∨ (¬ p1512) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p532) ∨ (¬ p63) ∨ p121 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1771 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1512 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p121) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19716 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u0)

theorem step29376 (p6 p41 p45 p127 p1718 p1771 p1798 : Prop)
    (h26831 : p45 ∨ p41)
    (h26839 : p127 ∨ p6)
    (h19268 : (¬ p45) ∨ (¬ p127) ∨ (¬ p1718) ∨ (¬ p1771) ∨ (¬ p1798)) : (¬ p1771) ∨ (¬ p1798) ∨ p41 ∨ p6 ∨ (¬ p1718) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1771 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1798 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1718 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19268 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)

theorem step29377 (p4 p8 p43 p134 p303 p310 p387 p421 p577 p1325 p1333 p1710 p1713 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26867 : p387 ∨ p303)
    (h18160 : (¬ p4) ∨ (¬ p8) ∨ (¬ p43) ∨ (¬ p134) ∨ (¬ p310) ∨ (¬ p387) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p1333) ∨ (¬ p1710) ∨ (¬ p1713)) : (¬ p1710) ∨ (¬ p1713) ∨ (¬ p310) ∨ (¬ p8) ∨ (¬ p134) ∨ (¬ p4) ∨ p1325 ∨ (¬ p43) ∨ p303 ∨ (¬ p421) ∨ (¬ p577) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1713 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u12 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h18160 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u12)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u11)
  · exact False.elim (q9 u0)
  · exact False.elim (q10 u1)

theorem step29378 (p43 p135 p283 p918 p928 p1710 p1713 : Prop)
    (h26901 : p928 ∨ p918)
    (h20042 : (¬ p43) ∨ (¬ p135) ∨ (¬ p283) ∨ (¬ p928) ∨ (¬ p1710) ∨ (¬ p1713)) : (¬ p1710) ∨ (¬ p1713) ∨ (¬ p283) ∨ (¬ p43) ∨ (¬ p135) ∨ p918 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1713 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p283 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20042 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u1)

theorem step29379 (p15 p49 p84 p185 p237 p980 p983 p1115 p1116 p1431 p1667 : Prop)
    (h26903 : p983 ∨ p980)
    (h26851 : p237 ∨ p185)
    (h26915 : p1116 ∨ p1115)
    (h20303 : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p237) ∨ (¬ p983) ∨ (¬ p1116) ∨ (¬ p1431) ∨ (¬ p1667)) : (¬ p1431) ∨ (¬ p1667) ∨ (¬ p15) ∨ (¬ p84) ∨ p980 ∨ (¬ p49) ∨ p185 ∨ p1115 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1667 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h20303 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u1)

theorem step29380 (p17 p256 p575 p918 p928 p1604 p1651 : Prop)
    (h26901 : p928 ∨ p918)
    (h26853 : p256 ∨ p17)
    (h17822 : (¬ p256) ∨ (¬ p575) ∨ (¬ p928) ∨ (¬ p1604) ∨ (¬ p1651)) : (¬ p1651) ∨ (¬ p1604) ∨ (¬ p575) ∨ p918 ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1651 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1604 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p575 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17822 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)

theorem step29381 (p17 p185 p255 p256 p757 p1651 : Prop)
    (h26853 : p256 ∨ p17)
    (h19978 : (¬ p185) ∨ (¬ p255) ∨ (¬ p256) ∨ (¬ p757) ∨ (¬ p1651)) : (¬ p757) ∨ (¬ p1651) ∨ (¬ p185) ∨ (¬ p255) ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p757 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1651 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p255 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19978 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)

theorem step29383 (p41 p45 p135 p580 p1611 p1644 : Prop)
    (h26831 : p45 ∨ p41)
    (h17654 : (¬ p45) ∨ (¬ p135) ∨ (¬ p580) ∨ (¬ p1611) ∨ (¬ p1644)) : (¬ p1644) ∨ (¬ p580) ∨ p41 ∨ (¬ p1611) ∨ (¬ p135) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1644 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p580 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1611 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17654 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u0)

theorem step29384 (p134 p210 p455 p456 p1611 p1624 : Prop)
    (h26871 : p456 ∨ p455)
    (h20297 : (¬ p134) ∨ (¬ p210) ∨ (¬ p456) ∨ (¬ p1611) ∨ (¬ p1624)) : (¬ p1611) ∨ (¬ p1624) ∨ (¬ p134) ∨ p455 ∨ (¬ p210) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1611 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1624 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p455) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20297 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)

theorem step29385 (p10 p25 p44 p171 p185 p237 p323 p521 p790 p814 p1611 p1666 : Prop)
    (h26851 : p237 ∨ p185)
    (h26893 : p814 ∨ p790)
    (h26861 : p323 ∨ p10)
    (h17810 : (¬ p25) ∨ (¬ p44) ∨ (¬ p171) ∨ (¬ p237) ∨ (¬ p323) ∨ (¬ p521) ∨ (¬ p814) ∨ (¬ p1611) ∨ (¬ p1666)) : (¬ p1611) ∨ (¬ p1666) ∨ (¬ p25) ∨ (¬ p44) ∨ p185 ∨ (¬ p521) ∨ (¬ p171) ∨ p790 ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1611 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1666 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p25 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p521 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p171 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h17810 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u0)
  · exact False.elim (q8 u1)

theorem step29386 (p495 p499 p635 p757 p1096 p1099 p1611 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26875 : p499 ∨ p495)
    (h16504 : (¬ p499) ∨ (¬ p635) ∨ (¬ p757) ∨ (¬ p1099) ∨ (¬ p1611)) : (¬ p757) ∨ (¬ p1611) ∨ (¬ p635) ∨ p1096 ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p757 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1611 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p635 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16504 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)

theorem step29388 (p41 p45 p171 p927 p1562 p1584 : Prop)
    (h26831 : p45 ∨ p41)
    (h17773 : (¬ p45) ∨ (¬ p171) ∨ (¬ p927) ∨ (¬ p1562) ∨ (¬ p1584)) : (¬ p1562) ∨ (¬ p1584) ∨ (¬ p927) ∨ p41 ∨ (¬ p171) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1562 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p927 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p171 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17773 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)

theorem step29390 (p15 p49 p927 p1115 p1116 p1229 p1232 p1313 p1562 p1584 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h26915 : p1116 ∨ p1115)
    (h16513 : (¬ p15) ∨ (¬ p49) ∨ (¬ p927) ∨ (¬ p1116) ∨ (¬ p1232) ∨ (¬ p1313) ∨ (¬ p1562) ∨ (¬ p1584)) : (¬ p1562) ∨ p1229 ∨ (¬ p1584) ∨ (¬ p927) ∨ (¬ p49) ∨ (¬ p15) ∨ p1115 ∨ (¬ p1313) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1562 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p927 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1313 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h16513 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u2)

theorem step29391 (p49 p63 p85 p423 p533 p1096 p1141 p1465 p1562 : Prop)
    (h26835 : p85 ∨ p63)
    (h26917 : p1141 ∨ p423)
    (h16633 : (¬ p49) ∨ (¬ p85) ∨ (¬ p533) ∨ (¬ p1096) ∨ (¬ p1141) ∨ (¬ p1465) ∨ (¬ p1562)) : (¬ p1562) ∨ p63 ∨ (¬ p1096) ∨ (¬ p49) ∨ (¬ p1465) ∨ (¬ p533) ∨ p423 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1562 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p63) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p423) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h16633 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u0)

theorem step29392 (p5 p6 p121 p532 p533 p1096 p1206 p1562 : Prop)
    (h26923 : p1206 ∨ p121)
    (h18949 : (¬ p5) ∨ (¬ p6) ∨ (¬ p532) ∨ (¬ p533) ∨ (¬ p1096) ∨ (¬ p1206) ∨ (¬ p1562)) : (¬ p1562) ∨ p121 ∨ (¬ p1096) ∨ (¬ p6) ∨ (¬ p532) ∨ (¬ p533) ∨ (¬ p5) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1562 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p121) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
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
  have u6 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18949 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u0)

theorem step29393 (p6 p38 p49 p121 p532 p836 p840 p927 p1206 p1562 p1584 : Prop)
    (h26895 : p840 ∨ p836)
    (h26923 : p1206 ∨ p121)
    (h16571 : (¬ p6) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p532) ∨ (¬ p840) ∨ (¬ p927) ∨ (¬ p1206) ∨ (¬ p1562) ∨ (¬ p1584)) : (¬ p1584) ∨ (¬ p1562) ∨ (¬ p532) ∨ p836 ∨ (¬ p38) ∨ p121 ∨ (¬ p49) ∨ (¬ p927) ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1562 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p121) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p927 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h16571 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u0)

theorem step29394 (p24 p41 p45 p125 p189 p193 p362 p420 p961 p1273 p1490 : Prop)
    (h26845 : p193 ∨ p189)
    (h26831 : p45 ∨ p41)
    (h26865 : p362 ∨ p125)
    (h19103 : (¬ p24) ∨ (¬ p45) ∨ (¬ p193) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p961) ∨ (¬ p1273) ∨ (¬ p1490)) : (¬ p1490) ∨ (¬ p420) ∨ p189 ∨ (¬ p961) ∨ (¬ p1273) ∨ p41 ∨ (¬ p24) ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1490 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h19103 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u0)

theorem step29395 (p4 p8 p189 p263 p303 p310 p387 p1325 p1333 p1473 p1711 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26867 : p387 ∨ p303)
    (h18159 : (¬ p4) ∨ (¬ p8) ∨ (¬ p189) ∨ (¬ p263) ∨ (¬ p310) ∨ (¬ p387) ∨ (¬ p1333) ∨ (¬ p1473) ∨ (¬ p1711)) : (¬ p1711) ∨ (¬ p263) ∨ (¬ p310) ∨ (¬ p4) ∨ (¬ p1473) ∨ (¬ p189) ∨ (¬ p8) ∨ p1325 ∨ p303 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1711 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p263 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1473 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h18159 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u0)

theorem step29396 (p15 p69 p124 p496 p980 p983 p1076 p1077 p1473 p1710 : Prop)
    (h26903 : p983 ∨ p980)
    (h26911 : p1077 ∨ p1076)
    (h26833 : p69 ∨ p15)
    (h19856 : (¬ p69) ∨ (¬ p124) ∨ (¬ p496) ∨ (¬ p983) ∨ (¬ p1077) ∨ (¬ p1473) ∨ (¬ p1710)) : (¬ p1710) ∨ (¬ p1473) ∨ (¬ p124) ∨ p980 ∨ (¬ p496) ∨ p1076 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1473 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u9 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19856 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u0)

theorem step29397 (p2 p64 p185 p234 p918 p928 p1254 p1346 p1471 p1710 : Prop)
    (h26901 : p928 ∨ p918)
    (h18716 : (¬ p2) ∨ (¬ p64) ∨ (¬ p185) ∨ (¬ p234) ∨ (¬ p928) ∨ (¬ p1254) ∨ (¬ p1346) ∨ (¬ p1471) ∨ (¬ p1710)) : (¬ p1710) ∨ (¬ p1471) ∨ (¬ p2) ∨ (¬ p1254) ∨ p918 ∨ (¬ p64) ∨ (¬ p185) ∨ (¬ p234) ∨ (¬ p1346) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1471 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1254 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18716 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u0)

theorem step29398 (p423 p980 p1044 p1141 p1470 p1712 : Prop)
    (h26917 : p1141 ∨ p423)
    (h18707 : (¬ p980) ∨ (¬ p1044) ∨ (¬ p1141) ∨ (¬ p1470) ∨ (¬ p1712)) : (¬ p1470) ∨ (¬ p1712) ∨ (¬ p980) ∨ p423 ∨ (¬ p1044) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1470 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1712 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p423) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1044 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18707 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)

theorem step29399 (p15 p18 p69 p980 p983 p1055 p1061 p1454 p1666 : Prop)
    (h26903 : p983 ∨ p980)
    (h26909 : p1061 ∨ p1055)
    (h26833 : p69 ∨ p15)
    (h22727 : (¬ p1454) ∨ (¬ p1666) ∨ (¬ p983) ∨ (¬ p69) ∨ (¬ p1061) ∨ (¬ p18)) : (¬ p1666) ∨ p980 ∨ p1055 ∨ p15 ∨ (¬ p1454) ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1666 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1454 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h22727 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u5)

theorem step29400 (p88 p134 p189 p924 p980 p983 p1055 p1061 p1098 p1454 p1666 : Prop)
    (h26903 : p983 ∨ p980)
    (h26909 : p1061 ∨ p1055)
    (h20017 : (¬ p88) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p924) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1098) ∨ (¬ p1454) ∨ (¬ p1666)) : (¬ p1454) ∨ (¬ p1666) ∨ (¬ p88) ∨ (¬ p924) ∨ (¬ p189) ∨ p980 ∨ p1055 ∨ (¬ p1098) ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1454 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1666 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1098 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20017 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u0)
  · exact False.elim (q8 u1)

theorem step29402 (p6 p38 p49 p88 p185 p237 p980 p983 p1115 p1116 p1454 p1666 : Prop)
    (h26851 : p237 ∨ p185)
    (h26903 : p983 ∨ p980)
    (h26915 : p1116 ∨ p1115)
    (h16502 : (¬ p6) ∨ (¬ p38) ∨ (¬ p49) ∨ p88 ∨ (¬ p237) ∨ (¬ p983) ∨ (¬ p1116) ∨ (¬ p1454) ∨ (¬ p1666)) : (¬ p1666) ∨ (¬ p1454) ∨ p185 ∨ p980 ∨ p88 ∨ p1115 ∨ (¬ p49) ∨ (¬ p6) ∨ (¬ p38) := by
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
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p88) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h16502 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u6)
  · exact False.elim (u4 q3)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u0)

theorem step29403 (p6 p63 p85 p88 p161 p194 p1225 p1229 p1454 p1666 : Prop)
    (h26925 : p1225 ∨ p161)
    (h26835 : p85 ∨ p63)
    (h18952 : (¬ p6) ∨ (¬ p85) ∨ (¬ p88) ∨ (¬ p194) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1454) ∨ (¬ p1666)) : (¬ p1666) ∨ (¬ p1454) ∨ (¬ p88) ∨ (¬ p1229) ∨ p161 ∨ (¬ p194) ∨ p63 ∨ (¬ p6) := by
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
  have u2 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p161) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18952 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u0)

theorem step29404 (p15 p17 p49 p84 p161 p256 p1229 p1232 p1449 p1651 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h26853 : p256 ∨ p17)
    (h18204 : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p161) ∨ (¬ p256) ∨ (¬ p1232) ∨ (¬ p1449) ∨ (¬ p1651)) : (¬ p1651) ∨ p1229 ∨ (¬ p84) ∨ p17 ∨ (¬ p1449) ∨ (¬ p161) ∨ (¬ p49) ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1651 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1449 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18204 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u0)

theorem step29450 (p63 p85 p620 p687 p1394 p1545 : Prop)
    (h26835 : p85 ∨ p63)
    (h19706 : (¬ p85) ∨ (¬ p620) ∨ (¬ p687) ∨ (¬ p1394) ∨ (¬ p1545)) : (¬ p687) ∨ (¬ p1545) ∨ (¬ p620) ∨ p63 ∨ (¬ p1394) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p620 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1394 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19706 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u1)

theorem step29476 (p41 p45 p382 p819 p1286 p1392 : Prop)
    (h26831 : p45 ∨ p41)
    (h25904 : (¬ p1286) ∨ (¬ p819) ∨ (¬ p382) ∨ (¬ p1392) ∨ (¬ p45)) : (¬ p1392) ∨ (¬ p819) ∨ (¬ p1286) ∨ (¬ p382) ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1392 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p819 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h25904 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)

theorem step29477 (p63 p85 p595 p616 p1387 : Prop)
    (h26882 : (¬ p595) ∨ (¬ p616))
    (h26835 : p85 ∨ p63)
    (h11318 : (¬ p85) ∨ p616 ∨ (¬ p1387)) : (¬ p595) ∨ p63 ∨ (¬ p1387) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p63) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p616) := by
    rcases h26882 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u4 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h11318 with q0 | q1 | q2
  · exact False.elim (q0 u4)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u2)

theorem step29479 (p576 p581 p789 p858 p1022 p1387 p1545 : Prop)
    (h26879 : p581 ∨ p576)
    (h26897 : p858 ∨ p789)
    (h19222 : (¬ p581) ∨ (¬ p858) ∨ (¬ p1022) ∨ (¬ p1387) ∨ (¬ p1545)) : (¬ p1022) ∨ (¬ p1387) ∨ (¬ p1545) ∨ p576 ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19222 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)

theorem step29480 (p90 p185 p237 p839 p1022 p1387 p1545 : Prop)
    (h26851 : p237 ∨ p185)
    (h26586 : p90)
    (h18477 : (¬ p90) ∨ (¬ p237) ∨ (¬ p839) ∨ (¬ p1022) ∨ (¬ p1387) ∨ (¬ p1545)) : (¬ p1022) ∨ p185 ∨ (¬ p839) ∨ (¬ p1545) ∨ (¬ p1387) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p839 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p90 := by
    exact h26586
  rcases h18477 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step29481 (p6 p10 p63 p85 p127 p303 p323 p387 p431 p1387 p1545 : Prop)
    (h26867 : p387 ∨ p303)
    (h26839 : p127 ∨ p6)
    (h26861 : p323 ∨ p10)
    (h26835 : p85 ∨ p63)
    (h25905 : (¬ p85) ∨ (¬ p431) ∨ (¬ p127) ∨ (¬ p1545) ∨ (¬ p1387) ∨ (¬ p387) ∨ (¬ p323)) : p303 ∨ p6 ∨ p10 ∨ p63 ∨ (¬ p1545) ∨ (¬ p431) ∨ (¬ p1387) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1545 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h25905 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u9)

theorem step29482 (p12 p13 p163 p189 p193 p1226 p1354 p1452 : Prop)
    (h26845 : p193 ∨ p189)
    (h16828 : (¬ p12) ∨ (¬ p13) ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p1226) ∨ (¬ p1354) ∨ (¬ p1452)) : (¬ p1452) ∨ (¬ p1226) ∨ (¬ p13) ∨ (¬ p163) ∨ p189 ∨ (¬ p12) ∨ (¬ p1354) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1354 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16828 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u0)

theorem step29485 (p41 p124 p160 p224 p304 p639 p897 p1000 p1250 p1348 p1465 : Prop)
    (h26859 : p304 ∨ p124)
    (h20087 : (¬ p41) ∨ (¬ p160) ∨ (¬ p224) ∨ (¬ p304) ∨ (¬ p639) ∨ (¬ p897) ∨ (¬ p1000) ∨ (¬ p1250) ∨ (¬ p1348) ∨ (¬ p1465)) : (¬ p160) ∨ p124 ∨ (¬ p639) ∨ (¬ p897) ∨ (¬ p1465) ∨ (¬ p1000) ∨ (¬ p1348) ∨ (¬ p41) ∨ (¬ p224) ∨ (¬ p1250) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p639 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1250 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20087 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u4)

theorem step29486 (p15 p69 p160 p234 p419 p665 p980 p1187 p1273 p1348 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26833 : p69 ∨ p15)
    (h18724 : (¬ p69) ∨ (¬ p160) ∨ (¬ p419) ∨ (¬ p665) ∨ (¬ p980) ∨ (¬ p1187) ∨ (¬ p1273) ∨ (¬ p1348)) : p234 ∨ (¬ p160) ∨ (¬ p980) ∨ p15 ∨ (¬ p1273) ∨ (¬ p1348) ∨ (¬ p419) ∨ (¬ p665) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p665 := by
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
    · exact False.elim (u3 q1)
  rcases h18724 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)

theorem step29487 (p84 p125 p185 p237 p425 p438 p582 p980 p983 p1115 p1116 p1335 : Prop)
    (h26903 : p983 ∨ p980)
    (h26851 : p237 ∨ p185)
    (h26915 : p1116 ∨ p1115)
    (h18759 : (¬ p84) ∨ (¬ p125) ∨ (¬ p237) ∨ (¬ p425) ∨ (¬ p438) ∨ (¬ p582) ∨ (¬ p983) ∨ (¬ p1116) ∨ (¬ p1335)) : p980 ∨ p185 ∨ (¬ p425) ∨ (¬ p582) ∨ (¬ p84) ∨ (¬ p438) ∨ p1115 ∨ (¬ p125) ∨ (¬ p1335) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u11 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18759 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u11)
  · exact False.elim (q8 u8)

theorem step29488 (p2 p11 p17 p194 p256 p435 p1335 p1443 p1452 : Prop)
    (h26853 : p256 ∨ p17)
    (h26935 : p1443 ∨ p11)
    (h17511 : (¬ p2) ∨ (¬ p194) ∨ (¬ p256) ∨ (¬ p435) ∨ (¬ p1335) ∨ (¬ p1443) ∨ (¬ p1452)) : (¬ p2) ∨ (¬ p194) ∨ (¬ p1452) ∨ p17 ∨ (¬ p1335) ∨ (¬ p435) ∨ p11 := by
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
  have u2 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h17511 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u2)

theorem step29510 (p84 p495 p499 p582 p980 p1229 p1232 p1313 p1346 p1508 : Prop)
    (h26875 : p499 ∨ p495)
    (h26927 : p1232 ∨ p1229)
    (h18744 : (¬ p84) ∨ (¬ p499) ∨ (¬ p582) ∨ (¬ p980) ∨ (¬ p1232) ∨ (¬ p1313) ∨ (¬ p1346) ∨ (¬ p1508)) : p495 ∨ (¬ p1346) ∨ (¬ p582) ∨ (¬ p1313) ∨ p1229 ∨ (¬ p84) ∨ (¬ p980) ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p495) := fun hu => hn (Or.inl hu)
  have u1 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1313 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18744 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u7)

theorem step29511 (p1096 p1229 p1232 p1311 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h9396 : (¬ p1096) ∨ (¬ p1232) ∨ (¬ p1311)) : p1229 ∨ (¬ p1311) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1229) := fun hu => hn (Or.inl hu)
  have u1 : p1311 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h9396 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)

theorem step29513 (p161 p668 p897 p980 p1225 p1311 : Prop)
    (h26925 : p1225 ∨ p161)
    (h20147 : (¬ p668) ∨ (¬ p897) ∨ (¬ p980) ∨ (¬ p1225) ∨ (¬ p1311)) : (¬ p980) ∨ (¬ p1311) ∨ (¬ p897) ∨ p161 ∨ (¬ p668) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1311 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p161) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20147 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)

theorem step29514 (p12 p886 p1036 p1096 p1099 p1229 p1310 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26907 : p1036 ∨ p12)
    (h20271 : (¬ p886) ∨ (¬ p1036) ∨ (¬ p1099) ∨ (¬ p1229) ∨ (¬ p1310)) : (¬ p1229) ∨ p1096 ∨ p12 ∨ (¬ p1310) ∨ (¬ p886) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p886 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20271 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u3)

theorem step29516 (p15 p39 p69 p88 p980 p983 p1229 p1309 p1349 p1489 : Prop)
    (h26903 : p983 ∨ p980)
    (h26833 : p69 ∨ p15)
    (h20461 : (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p983) ∨ (¬ p1229) ∨ (¬ p1309) ∨ (¬ p1349) ∨ (¬ p1489)) : (¬ p1489) ∨ p980 ∨ (¬ p1229) ∨ (¬ p88) ∨ (¬ p1349) ∨ (¬ p39) ∨ p15 ∨ (¬ p1309) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20461 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u0)

theorem step29518 (p664 p897 p904 p1096 p1229 p1232 p1307 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h26899 : p904 ∨ p897)
    (h16395 : (¬ p664) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1232) ∨ (¬ p1307)) : p1229 ∨ (¬ p1307) ∨ p897 ∨ (¬ p1096) ∨ (¬ p664) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1229) := fun hu => hn (Or.inl hu)
  have u1 : p1307 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16395 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)

theorem step29519 (p12 p882 p1096 p1229 p1232 p1307 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h16469 : (¬ p12) ∨ (¬ p882) ∨ (¬ p1096) ∨ (¬ p1232) ∨ (¬ p1307)) : (¬ p882) ∨ p1229 ∨ (¬ p12) ∨ (¬ p1307) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p882 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1307 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16469 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)

theorem step29520 (p925 p1096 p1115 p1116 p1229 p1232 p1307 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h26915 : p1116 ∨ p1115)
    (h19050 : (¬ p925) ∨ (¬ p1096) ∨ (¬ p1116) ∨ (¬ p1232) ∨ (¬ p1307)) : p1229 ∨ (¬ p925) ∨ p1115 ∨ (¬ p1307) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1229) := fun hu => hn (Or.inl hu)
  have u1 : p925 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1307 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19050 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)

theorem step29523 (p15 p49 p84 p124 p224 p266 p344 p657 p1229 p1232 p1295 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h26887 : p657 ∨ p224)
    (h18196 : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p124) ∨ (¬ p266) ∨ (¬ p344) ∨ (¬ p657) ∨ (¬ p1232) ∨ (¬ p1295)) : (¬ p1295) ∨ p1229 ∨ (¬ p15) ∨ (¬ p84) ∨ (¬ p266) ∨ (¬ p49) ∨ (¬ p344) ∨ (¬ p124) ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1295 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h18196 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u0)

theorem step29524 (p63 p85 p124 p224 p304 p344 p346 p425 p582 p1229 p1291 : Prop)
    (h26859 : p304 ∨ p124)
    (h26863 : p346 ∨ p344)
    (h26835 : p85 ∨ p63)
    (h16793 : (¬ p85) ∨ (¬ p224) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p425) ∨ (¬ p582) ∨ (¬ p1229) ∨ (¬ p1291)) : p124 ∨ p344 ∨ (¬ p1229) ∨ p63 ∨ (¬ p425) ∨ (¬ p1291) ∨ (¬ p224) ∨ (¬ p582) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1291 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16793 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u5)

theorem step29525 (p224 p595 p657 p901 p1229 p1232 p1289 : Prop)
    (h26887 : p657 ∨ p224)
    (h26927 : p1232 ∨ p1229)
    (h16471 : (¬ p595) ∨ (¬ p657) ∨ (¬ p901) ∨ (¬ p1232) ∨ (¬ p1289)) : (¬ p901) ∨ p224 ∨ p1229 ∨ (¬ p595) ∨ (¬ p1289) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p901 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1289 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16471 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u4)

theorem step29527 (p303 p387 p595 p599 p1229 p1232 p1289 : Prop)
    (h26867 : p387 ∨ p303)
    (h26927 : p1232 ∨ p1229)
    (h16490 : (¬ p387) ∨ (¬ p595) ∨ (¬ p599) ∨ (¬ p1232) ∨ (¬ p1289)) : p303 ∨ (¬ p599) ∨ (¬ p1289) ∨ p1229 ∨ (¬ p595) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p599 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1289 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16490 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u2)

theorem step29528 (p161 p1225 p1289 p1325 : Prop)
    (h26925 : p1225 ∨ p161)
    (h9341 : (¬ p1225) ∨ (¬ p1289) ∨ (¬ p1325)) : p161 ∨ (¬ p1289) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p161) := fun hu => hn (Or.inl hu)
  have u1 : p1289 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h9341 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)

theorem step29530 (p419 p595 p996 p1191 p1229 p1232 p1289 : Prop)
    (h26905 : p996 ∨ p419)
    (h26927 : p1232 ∨ p1229)
    (h16462 : (¬ p595) ∨ (¬ p996) ∨ (¬ p1191) ∨ (¬ p1232) ∨ (¬ p1289)) : (¬ p1191) ∨ p419 ∨ (¬ p1289) ∨ (¬ p595) ∨ p1229 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p419) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1289 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16462 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u2)

theorem step29532 (p6 p18 p19 p48 p64 p1229 p1274 : Prop)
    (h26829 : p19 ∨ p18)
    (h16761 : (¬ p6) ∨ (¬ p19) ∨ (¬ p48) ∨ (¬ p64) ∨ (¬ p1229) ∨ (¬ p1274)) : (¬ p48) ∨ (¬ p64) ∨ (¬ p1274) ∨ (¬ p6) ∨ (¬ p1229) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1274 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h16761 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u2)

theorem step29533 (p14 p15 p63 p85 p109 p161 p1035 p1212 p1274 : Prop)
    (h26835 : p85 ∨ p63)
    (h16549 : (¬ p14) ∨ (¬ p15) ∨ (¬ p85) ∨ (¬ p109) ∨ (¬ p161) ∨ (¬ p1035) ∨ (¬ p1212) ∨ (¬ p1274)) : (¬ p1035) ∨ (¬ p1274) ∨ (¬ p15) ∨ p63 ∨ (¬ p109) ∨ (¬ p14) ∨ (¬ p1212) ∨ (¬ p161) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1274 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p109 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1212 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16549 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u1)

theorem step29560 (p6 p127 p1140 p1159 p1255 p1273 p1385 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26839 : p127 ∨ p6)
    (h20214 : (¬ p127) ∨ (¬ p1159) ∨ (¬ p1255) ∨ (¬ p1273) ∨ (¬ p1385)) : (¬ p1255) ∨ (¬ p1385) ∨ p1140 ∨ p6 ∨ (¬ p1273) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1255 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20214 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u1)

theorem step29561 (p18 p189 p193 p423 p1253 p1349 : Prop)
    (h26845 : p193 ∨ p189)
    (h18258 : (¬ p18) ∨ (¬ p193) ∨ (¬ p423) ∨ (¬ p1253) ∨ (¬ p1349)) : (¬ p1253) ∨ (¬ p1349) ∨ (¬ p423) ∨ p189 ∨ (¬ p18) := by
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
  have u2 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18258 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)

theorem step29562 (p41 p45 p124 p189 p193 p224 p344 p657 p1004 p1253 p1349 : Prop)
    (h26845 : p193 ∨ p189)
    (h26831 : p45 ∨ p41)
    (h26887 : p657 ∨ p224)
    (h19461 : (¬ p45) ∨ (¬ p124) ∨ (¬ p193) ∨ (¬ p344) ∨ (¬ p657) ∨ (¬ p1004) ∨ (¬ p1253) ∨ (¬ p1349)) : (¬ p1253) ∨ (¬ p1004) ∨ p189 ∨ (¬ p1349) ∨ p41 ∨ (¬ p124) ∨ p224 ∨ (¬ p344) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1253 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19461 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u3)

theorem step29564 (p41 p45 p1252 p1273 : Prop)
    (h26831 : p45 ∨ p41)
    (h12368 : (¬ p45) ∨ (¬ p1252) ∨ (¬ p1273)) : (¬ p1252) ∨ (¬ p1273) ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1252 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h12368 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)

theorem step29567 (p41 p63 p1229 p1232 p1251 p1269 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h18352 : (¬ p41) ∨ (¬ p63) ∨ (¬ p1232) ∨ (¬ p1251) ∨ (¬ p1269)) : (¬ p1251) ∨ p1229 ∨ (¬ p41) ∨ (¬ p1269) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1251 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1269 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18352 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u3)

theorem step29570 (p10 p41 p121 p125 p159 p160 p161 p323 p1206 p1236 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26861 : p323 ∨ p10)
    (h25927 : (¬ p1206) ∨ (¬ p160) ∨ (¬ p161) ∨ (¬ p323) ∨ (¬ p159) ∨ (¬ p125) ∨ (¬ p41) ∨ (¬ p1236)) : (¬ p1236) ∨ (¬ p160) ∨ (¬ p125) ∨ (¬ p161) ∨ (¬ p41) ∨ p121 ∨ p10 ∨ (¬ p159) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1236 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p121) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u9 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h25927 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u0)

theorem step29571 (p63 p1227 p1229 p1232 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h8742 : (¬ p63) ∨ (¬ p1227) ∨ (¬ p1232)) : (¬ p1227) ∨ p1229 ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h8742 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)

theorem step29572 (p3 p5 p12 p63 p161 p226 p1036 p1120 p1225 p1227 p1489 : Prop)
    (h26847 : p226 ∨ p3)
    (h26907 : p1036 ∨ p12)
    (h26925 : p1225 ∨ p161)
    (h18077 : (¬ p5) ∨ (¬ p63) ∨ (¬ p226) ∨ (¬ p1036) ∨ (¬ p1120) ∨ (¬ p1225) ∨ (¬ p1227) ∨ (¬ p1489)) : (¬ p1489) ∨ (¬ p1120) ∨ (¬ p5) ∨ p3 ∨ (¬ p1227) ∨ p12 ∨ p161 ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1120 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p161) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18077 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u0)

theorem step29574 (p15 p49 p161 p1225 p1226 p1227 p1230 : Prop)
    (h26925 : p1225 ∨ p161)
    (h16352 : (¬ p15) ∨ (¬ p49) ∨ (¬ p1225) ∨ (¬ p1226) ∨ (¬ p1227) ∨ (¬ p1230)) : (¬ p1226) ∨ p161 ∨ (¬ p1230) ∨ (¬ p1227) ∨ (¬ p49) ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p161) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1230 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16352 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u2)

theorem step29577 (p2 p64 p124 p227 p234 p304 p423 p633 p1141 p1214 : Prop)
    (h26859 : p304 ∨ p124)
    (h26917 : p1141 ∨ p423)
    (h16901 : (¬ p2) ∨ (¬ p64) ∨ (¬ p227) ∨ (¬ p234) ∨ (¬ p304) ∨ (¬ p633) ∨ (¬ p1141) ∨ (¬ p1214)) : (¬ p227) ∨ (¬ p2) ∨ (¬ p234) ∨ p124 ∨ p423 ∨ (¬ p633) ∨ (¬ p64) ∨ (¬ p1214) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p423) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1214 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16901 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u7)

theorem step29578 (p10 p41 p45 p63 p85 p125 p227 p323 p422 p1214 : Prop)
    (h26861 : p323 ∨ p10)
    (h26835 : p85 ∨ p63)
    (h26831 : p45 ∨ p41)
    (h19968 : (¬ p45) ∨ (¬ p85) ∨ (¬ p125) ∨ (¬ p227) ∨ (¬ p323) ∨ (¬ p422) ∨ (¬ p1214)) : (¬ p125) ∨ (¬ p422) ∨ (¬ p227) ∨ p10 ∨ p63 ∨ (¬ p1214) ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1214 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19968 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u5)

theorem step29580 (p15 p69 p620 p687 p1194 p1545 : Prop)
    (h26833 : p69 ∨ p15)
    (h16717 : (¬ p69) ∨ (¬ p620) ∨ (¬ p687) ∨ (¬ p1194) ∨ (¬ p1545)) : (¬ p687) ∨ (¬ p1194) ∨ p15 ∨ (¬ p620) ∨ (¬ p1545) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p620 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16717 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)

theorem step29581 (p422 p424 p796 p1001 p1191 p1256 p1287 : Prop)
    (h26891 : p796 ∨ p424)
    (h26929 : p1256 ∨ p422)
    (h17926 : (¬ p796) ∨ (¬ p1001) ∨ (¬ p1191) ∨ (¬ p1256) ∨ (¬ p1287)) : p424 ∨ p422 ∨ (¬ p1191) ∨ (¬ p1001) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p422) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1001 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17926 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u4)

theorem step29582 (p160 p161 p401 p419 p996 p1191 p1288 : Prop)
    (h26905 : p996 ∨ p419)
    (h17934 : (¬ p160) ∨ (¬ p161) ∨ (¬ p401) ∨ (¬ p996) ∨ (¬ p1191) ∨ (¬ p1288)) : p419 ∨ (¬ p160) ∨ (¬ p1288) ∨ (¬ p1191) ∨ (¬ p161) ∨ (¬ p401) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p401 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17934 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u2)

theorem step29584 (p15 p49 p435 p595 p616 p1189 p1273 p1335 p1508 : Prop)
    (h26883 : p616 ∨ p595)
    (h16361 : (¬ p15) ∨ (¬ p49) ∨ (¬ p435) ∨ (¬ p616) ∨ (¬ p1189) ∨ (¬ p1273) ∨ (¬ p1335) ∨ (¬ p1508)) : (¬ p1189) ∨ (¬ p1273) ∨ (¬ p1335) ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p435) ∨ (¬ p1508) ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h16361 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u6)

theorem step29606 (p18 p19 p424 p1188 p1366 p1545 : Prop)
    (h26829 : p19 ∨ p18)
    (h20504 : (¬ p19) ∨ (¬ p424) ∨ (¬ p1188) ∨ (¬ p1366) ∨ (¬ p1545)) : (¬ p1188) ∨ p18 ∨ (¬ p1366) ∨ (¬ p424) ∨ (¬ p1545) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p18) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20504 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u4)

theorem step29607 (p14 p109 p207 p368 p382 p406 p1188 p1287 : Prop)
    (h26869 : p406 ∨ p382)
    (h17964 : (¬ p14) ∨ (¬ p109) ∨ (¬ p207) ∨ (¬ p368) ∨ (¬ p406) ∨ (¬ p1188) ∨ (¬ p1287)) : (¬ p1188) ∨ p382 ∨ (¬ p109) ∨ (¬ p368) ∨ (¬ p207) ∨ (¬ p1287) ∨ (¬ p14) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p109 := by
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
  have u5 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17964 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u5)

theorem step29608 (p18 p19 p105 p382 p406 p557 p680 p1188 p1287 : Prop)
    (h26829 : p19 ∨ p18)
    (h26869 : p406 ∨ p382)
    (h20525 : (¬ p19) ∨ (¬ p105) ∨ (¬ p406) ∨ (¬ p557) ∨ (¬ p680) ∨ (¬ p1188) ∨ (¬ p1287)) : (¬ p557) ∨ (¬ p105) ∨ (¬ p1188) ∨ p18 ∨ (¬ p680) ∨ (¬ p1287) ∨ p382 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20525 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u5)

theorem step29609 (p18 p19 p326 p382 p406 p476 p1188 p1287 : Prop)
    (h26869 : p406 ∨ p382)
    (h26829 : p19 ∨ p18)
    (h20498 : (¬ p19) ∨ (¬ p326) ∨ (¬ p406) ∨ (¬ p476) ∨ (¬ p1188) ∨ (¬ p1287)) : p382 ∨ (¬ p1188) ∨ p18 ∨ (¬ p326) ∨ (¬ p1287) ∨ (¬ p476) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p1188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p326 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p476 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20498 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u4)

theorem step29610 (p3 p14 p188 p226 p419 p996 p1188 p1287 : Prop)
    (h26847 : p226 ∨ p3)
    (h26905 : p996 ∨ p419)
    (h18981 : (¬ p14) ∨ (¬ p188) ∨ (¬ p226) ∨ (¬ p996) ∨ (¬ p1188) ∨ (¬ p1287)) : p3 ∨ (¬ p1188) ∨ (¬ p14) ∨ (¬ p1287) ∨ p419 ∨ (¬ p188) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p1188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18981 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u3)

theorem step29611 (p2 p18 p19 p419 p481 p996 p1188 p1287 : Prop)
    (h26905 : p996 ∨ p419)
    (h26873 : p481 ∨ p2)
    (h26829 : p19 ∨ p18)
    (h20548 : (¬ p19) ∨ (¬ p481) ∨ (¬ p996) ∨ (¬ p1188) ∨ (¬ p1287)) : (¬ p1188) ∨ p419 ∨ p2 ∨ p18 ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p419) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20548 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)

theorem step29613 (p14 p423 p980 p983 p1141 p1167 p1226 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26903 : p983 ∨ p980)
    (h20409 : (¬ p14) ∨ (¬ p983) ∨ (¬ p1141) ∨ (¬ p1167) ∨ (¬ p1226)) : p423 ∨ p980 ∨ (¬ p1167) ∨ (¬ p1226) ∨ (¬ p14) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20409 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)

theorem step29614 (p10 p185 p189 p237 p323 p665 p1115 p1116 p1167 p1207 p1226 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26915 : p1116 ∨ p1115)
    (h26861 : p323 ∨ p10)
    (h26851 : p237 ∨ p185)
    (h19184 : (¬ p189) ∨ (¬ p237) ∨ (¬ p323) ∨ (¬ p665) ∨ (¬ p1116) ∨ (¬ p1167) ∨ (¬ p1207) ∨ (¬ p1226) ∨ (¬ p1333)) : p1325 ∨ (¬ p1167) ∨ p1115 ∨ p10 ∨ (¬ p189) ∨ (¬ p1207) ∨ (¬ p665) ∨ p185 ∨ (¬ p1226) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1325) := fun hu => hn (Or.inl hu)
  have u1 : p1167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u12 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h19184 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u12)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u9)

theorem step29615 (p3 p72 p423 p728 p880 p897 p904 p1141 p1167 p1226 p1330 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26899 : p904 ∨ p897)
    (h20581 : (¬ p3) ∨ (¬ p72) ∨ (¬ p728) ∨ (¬ p880) ∨ (¬ p904) ∨ (¬ p1141) ∨ (¬ p1167) ∨ (¬ p1226) ∨ (¬ p1330)) : p423 ∨ (¬ p1167) ∨ p897 ∨ (¬ p1330) ∨ (¬ p1226) ∨ (¬ p72) ∨ (¬ p3) ∨ (¬ p728) ∨ (¬ p880) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p1167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p880 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20581 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u3)

theorem step29616 (p101 p102 p121 p124 p160 p206 p304 p1165 p1206 p1489 p1490 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26859 : p304 ∨ p124)
    (h26837 : p102 ∨ p101)
    (h16387 : (¬ p102) ∨ (¬ p160) ∨ (¬ p206) ∨ (¬ p304) ∨ (¬ p1165) ∨ (¬ p1206) ∨ (¬ p1489) ∨ (¬ p1490)) : (¬ p1165) ∨ (¬ p160) ∨ (¬ p1489) ∨ p121 ∨ (¬ p1490) ∨ p124 ∨ (¬ p206) ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1165 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p121) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1490 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h16387 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u4)

theorem step29638 (p18 p161 p1146 p1213 p1225 p1465 : Prop)
    (h26925 : p1225 ∨ p161)
    (h18108 : (¬ p18) ∨ (¬ p1146) ∨ (¬ p1213) ∨ (¬ p1225) ∨ (¬ p1465)) : p161 ∨ (¬ p18) ∨ (¬ p1213) ∨ (¬ p1146) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p161) := fun hu => hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1213 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1146 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h18108 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)

theorem step29639 (p15 p1146 p1229 p1232 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h8780 : (¬ p15) ∨ (¬ p1146) ∨ (¬ p1232)) : p1229 ∨ (¬ p1146) ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1229) := fun hu => hn (Or.inl hu)
  have u1 : p1146 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8780 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)

theorem step29640 (p50 p161 p422 p1146 p1225 p1465 : Prop)
    (h26925 : p1225 ∨ p161)
    (h16998 : (¬ p50) ∨ (¬ p422) ∨ (¬ p1146) ∨ (¬ p1225) ∨ (¬ p1465)) : (¬ p422) ∨ p161 ∨ (¬ p1146) ∨ (¬ p50) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p161) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1146 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p50 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16998 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)

theorem step29641 (p161 p1142 p1225 p1465 : Prop)
    (h26925 : p1225 ∨ p161)
    (h11346 : (¬ p1142) ∨ (¬ p1225) ∨ (¬ p1465)) : (¬ p1142) ∨ p161 ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p161) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h11346 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)

theorem step29642 (p15 p18 p19 p1142 p1209 p1229 p1232 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h26829 : p19 ∨ p18)
    (h16520 : (¬ p15) ∨ (¬ p19) ∨ (¬ p1142) ∨ (¬ p1209) ∨ (¬ p1232)) : (¬ p15) ∨ (¬ p1142) ∨ p1229 ∨ (¬ p1209) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16520 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)

theorem step29643 (p15 p422 p1142 p1229 p1232 p1256 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h26929 : p1256 ∨ p422)
    (h25929 : (¬ p1232) ∨ (¬ p1142) ∨ (¬ p1256) ∨ (¬ p15)) : (¬ p1142) ∨ p1229 ∨ p422 ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h25929 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)

theorem step29644 (p12 p14 p15 p69 p161 p229 p422 p1036 p1142 p1225 p1256 p1325 : Prop)
    (h26907 : p1036 ∨ p12)
    (h26925 : p1225 ∨ p161)
    (h26849 : p229 ∨ p14)
    (h26833 : p69 ∨ p15)
    (h26929 : p1256 ∨ p422)
    (h25930 : (¬ p1225) ∨ (¬ p1142) ∨ (¬ p1256) ∨ (¬ p1036) ∨ (¬ p69) ∨ (¬ p1325) ∨ (¬ p229)) : (¬ p1142) ∨ p12 ∨ p161 ∨ p14 ∨ p15 ∨ p422 ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p161) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h25930 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u9)

theorem step29645 (p11 p13 p63 p85 p161 p422 p576 p980 p1142 p1225 p1256 : Prop)
    (h26835 : p85 ∨ p63)
    (h26925 : p1225 ∨ p161)
    (h26929 : p1256 ∨ p422)
    (h19869 : (¬ p11) ∨ (¬ p13) ∨ (¬ p85) ∨ (¬ p576) ∨ (¬ p980) ∨ (¬ p1142) ∨ (¬ p1225) ∨ (¬ p1256)) : (¬ p1142) ∨ (¬ p980) ∨ (¬ p13) ∨ (¬ p11) ∨ (¬ p576) ∨ p63 ∨ p161 ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p161) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u9 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h19869 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u10)

theorem step29646 (p63 p85 p980 p1035 p1124 p1140 p1249 : Prop)
    (h26835 : p85 ∨ p63)
    (h25931 : (¬ p1035) ∨ (¬ p1124) ∨ (¬ p1140) ∨ (¬ p980) ∨ (¬ p85) ∨ (¬ p1249)) : (¬ p1140) ∨ (¬ p1035) ∨ (¬ p1249) ∨ (¬ p980) ∨ p63 ∨ (¬ p1124) := by
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
  have u2 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h25931 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)

theorem step29648 (p138 p189 p193 p262 p368 p382 p384 p406 p980 p1124 p1349 p1452 : Prop)
    (h26869 : p406 ∨ p382)
    (h26845 : p193 ∨ p189)
    (h19940 : (¬ p138) ∨ (¬ p193) ∨ (¬ p262) ∨ (¬ p368) ∨ (¬ p384) ∨ (¬ p406) ∨ (¬ p980) ∨ (¬ p1124) ∨ (¬ p1349) ∨ (¬ p1452)) : p382 ∨ (¬ p1452) ∨ (¬ p1124) ∨ (¬ p262) ∨ p189 ∨ (¬ p384) ∨ (¬ p368) ∨ (¬ p1349) ∨ (¬ p980) ∨ (¬ p138) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p384 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u11 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19940 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u11)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u2)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u1)

theorem step29652 (p86 p185 p237 p595 p616 p665 p980 p1122 p1287 p1508 : Prop)
    (h26851 : p237 ∨ p185)
    (h26883 : p616 ∨ p595)
    (h18810 : (¬ p86) ∨ (¬ p237) ∨ (¬ p616) ∨ (¬ p665) ∨ (¬ p980) ∨ (¬ p1122) ∨ (¬ p1287) ∨ (¬ p1508)) : (¬ p1508) ∨ p185 ∨ (¬ p665) ∨ (¬ p1122) ∨ (¬ p980) ∨ p595 ∨ (¬ p86) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1122 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18810 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u0)

theorem step29654 (p161 p790 p814 p980 p983 p1120 p1229 p1232 p1346 p1385 p1393 : Prop)
    (h26903 : p983 ∨ p980)
    (h26927 : p1232 ∨ p1229)
    (h26893 : p814 ∨ p790)
    (h26933 : p1393 ∨ p1385)
    (h19686 : (¬ p161) ∨ (¬ p814) ∨ (¬ p983) ∨ (¬ p1120) ∨ (¬ p1232) ∨ (¬ p1346) ∨ (¬ p1393)) : p980 ∨ (¬ p1346) ∨ p1229 ∨ p790 ∨ (¬ p161) ∨ p1385 ∨ (¬ p1120) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1120 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19686 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u10)

theorem step29655 (p41 p45 p89 p189 p193 p980 p983 p1120 p1226 p1237 p1273 : Prop)
    (h26903 : p983 ∨ p980)
    (h26845 : p193 ∨ p189)
    (h26831 : p45 ∨ p41)
    (h17428 : (¬ p45) ∨ (¬ p89) ∨ (¬ p193) ∨ (¬ p983) ∨ (¬ p1120) ∨ (¬ p1226) ∨ (¬ p1237) ∨ (¬ p1273)) : p980 ∨ (¬ p1120) ∨ (¬ p89) ∨ (¬ p1237) ∨ (¬ p1226) ∨ (¬ p1273) ∨ p189 ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : p1120 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h17428 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u5)

theorem step29656 (p15 p49 p161 p635 p1076 p1096 p1099 p1120 p1225 p1227 p1489 : Prop)
    (h26925 : p1225 ∨ p161)
    (h26913 : p1099 ∨ p1096)
    (h16400 : (¬ p15) ∨ (¬ p49) ∨ (¬ p635) ∨ (¬ p1076) ∨ (¬ p1099) ∨ (¬ p1120) ∨ (¬ p1225) ∨ (¬ p1227) ∨ (¬ p1489)) : (¬ p1120) ∨ p161 ∨ p1096 ∨ (¬ p1076) ∨ (¬ p15) ∨ (¬ p635) ∨ (¬ p49) ∨ (¬ p1489) ∨ (¬ p1227) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1120 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p161) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p635 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16400 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u7)

theorem step29659 (p12 p166 p1036 p1115 : Prop)
    (h26907 : p1036 ∨ p12)
    (h15112 : (¬ p166) ∨ (¬ p1036) ∨ p1115) : (¬ p166) ∨ p12 ∨ p1115 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p166 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h15112 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (u2 q2)

theorem step29660 (p8 p161 p224 p228 p532 p710 p1103 p1225 p1229 : Prop)
    (h26925 : p1225 ∨ p161)
    (h26889 : p710 ∨ p8)
    (h19973 : (¬ p224) ∨ (¬ p228) ∨ (¬ p532) ∨ (¬ p710) ∨ (¬ p1103) ∨ (¬ p1225) ∨ (¬ p1229)) : p161 ∨ (¬ p1229) ∨ p8 ∨ (¬ p1103) ∨ (¬ p224) ∨ (¬ p228) ∨ (¬ p532) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p161) := fun hu => hn (Or.inl hu)
  have u1 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19973 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step29661 (p41 p63 p106 p163 p1055 p1076 p1077 p1103 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h18637 : (¬ p41) ∨ (¬ p63) ∨ (¬ p106) ∨ (¬ p163) ∨ (¬ p1055) ∨ (¬ p1077) ∨ (¬ p1103)) : (¬ p41) ∨ (¬ p1055) ∨ p1076 ∨ (¬ p63) ∨ (¬ p106) ∨ (¬ p1103) ∨ (¬ p163) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18637 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u5)

theorem step29662 (p8 p11 p63 p85 p224 p389 p576 p657 : Prop)
    (h26835 : p85 ∨ p63)
    (h26887 : p657 ∨ p224)
    (h22729 : (¬ p389) ∨ (¬ p576) ∨ (¬ p85) ∨ (¬ p11) ∨ (¬ p657) ∨ (¬ p8)) : (¬ p11) ∨ (¬ p389) ∨ (¬ p8) ∨ (¬ p576) ∨ p63 ∨ p224 := by
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
  have u2 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u7 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h22729 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)

theorem step29663 (p8 p41 p45 p63 p85 p134 p224 p657 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26831 : p45 ∨ p41)
    (h26887 : p657 ∨ p224)
    (h26835 : p85 ∨ p63)
    (h22730 : (¬ p45) ∨ (¬ p657) ∨ (¬ p8) ∨ (¬ p134) ∨ (¬ p85) ∨ (¬ p1333)) : p1325 ∨ p41 ∨ p224 ∨ (¬ p134) ∨ (¬ p8) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1325) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p41) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h22730 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u6)

theorem step29664 (p8 p124 p304 p344 p346 p494 : Prop)
    (h26859 : p304 ∨ p124)
    (h26863 : p346 ∨ p344)
    (h22731 : (¬ p346) ∨ (¬ p494) ∨ (¬ p304) ∨ (¬ p8)) : p124 ∨ p344 ∨ (¬ p8) ∨ (¬ p494) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h22731 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)

theorem step29665 (p8 p41 p83 p189 p290 p344 p346 p918 : Prop)
    (h26863 : p346 ∨ p344)
    (h22732 : (¬ p346) ∨ (¬ p290) ∨ (¬ p918) ∨ (¬ p189) ∨ (¬ p8) ∨ (¬ p41) ∨ (¬ p83)) : (¬ p918) ∨ (¬ p41) ∨ (¬ p290) ∨ p344 ∨ (¬ p83) ∨ (¬ p189) ∨ (¬ p8) := by
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
  have u2 : p290 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h22732 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u4)

theorem step29666 (p536 p595 p616 p836 p840 p1287 p1325 p1584 : Prop)
    (h26895 : p840 ∨ p836)
    (h26883 : p616 ∨ p595)
    (h22733 : (¬ p1584) ∨ (¬ p536) ∨ (¬ p840) ∨ (¬ p616) ∨ (¬ p1287) ∨ (¬ p1325)) : (¬ p536) ∨ (¬ p1584) ∨ (¬ p1325) ∨ (¬ p1287) ∨ p836 ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p536 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u7 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h22733 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u2)

theorem step29667 (p8 p41 p45 p63 p85 p134 p344 p346 p1076 p1077 : Prop)
    (h26831 : p45 ∨ p41)
    (h26911 : p1077 ∨ p1076)
    (h26835 : p85 ∨ p63)
    (h26863 : p346 ∨ p344)
    (h22734 : (¬ p346) ∨ (¬ p45) ∨ (¬ p134) ∨ (¬ p8) ∨ (¬ p1077) ∨ (¬ p85)) : p41 ∨ p1076 ∨ (¬ p8) ∨ p63 ∨ p344 ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p41) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h22734 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u8)

theorem step29668 (p8 p15 p69 p423 p728 p1141 p1330 p1465 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26833 : p69 ∨ p15)
    (h22735 : (¬ p728) ∨ (¬ p69) ∨ (¬ p8) ∨ (¬ p1330) ∨ (¬ p1141) ∨ (¬ p1465)) : p423 ∨ (¬ p728) ∨ (¬ p1465) ∨ (¬ p1330) ∨ (¬ p8) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h22735 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)

theorem step29669 (p8 p224 p420 p431 p438 p495 p657 : Prop)
    (h26887 : p657 ∨ p224)
    (h22736 : (¬ p420) ∨ (¬ p495) ∨ (¬ p431) ∨ (¬ p8) ∨ (¬ p657) ∨ (¬ p438)) : (¬ p420) ∨ (¬ p431) ∨ (¬ p438) ∨ (¬ p8) ∨ (¬ p495) ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h22736 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)

theorem step29670 (p8 p455 p456 p495 p532 p728 p1330 : Prop)
    (h26871 : p456 ∨ p455)
    (h22737 : (¬ p532) ∨ (¬ p728) ∨ (¬ p1330) ∨ (¬ p456) ∨ (¬ p8) ∨ (¬ p495)) : p455 ∨ (¬ p8) ∨ (¬ p1330) ∨ (¬ p728) ∨ (¬ p495) ∨ (¬ p532) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h22737 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u4)

theorem step29671 (p8 p15 p49 p710 p897 p904 p927 p1097 : Prop)
    (h26899 : p904 ∨ p897)
    (h26889 : p710 ∨ p8)
    (h16443 : (¬ p15) ∨ (¬ p49) ∨ (¬ p710) ∨ (¬ p904) ∨ (¬ p927) ∨ (¬ p1097)) : p897 ∨ p8 ∨ (¬ p49) ∨ (¬ p15) ∨ (¬ p1097) ∨ (¬ p927) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p897) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p8) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1097 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p927 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16443 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u4)

theorem step29672 (p63 p85 p125 p227 p420 p601 p918 p1081 p1115 : Prop)
    (h26835 : p85 ∨ p63)
    (h26881 : p601 ∨ p420)
    (h19775 : (¬ p85) ∨ (¬ p125) ∨ (¬ p227) ∨ (¬ p601) ∨ (¬ p918) ∨ (¬ p1081) ∨ (¬ p1115)) : (¬ p125) ∨ (¬ p1115) ∨ (¬ p227) ∨ p63 ∨ p420 ∨ (¬ p1081) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19775 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u1)

theorem step29673 (p3 p18 p19 p67 p161 p207 p226 p227 p883 p980 p983 p1081 p1306 : Prop)
    (h26847 : p226 ∨ p3)
    (h26903 : p983 ∨ p980)
    (h26829 : p19 ∨ p18)
    (h18030 : (¬ p19) ∨ (¬ p67) ∨ (¬ p161) ∨ (¬ p207) ∨ (¬ p226) ∨ (¬ p227) ∨ (¬ p883) ∨ (¬ p983) ∨ (¬ p1081) ∨ (¬ p1306)) : (¬ p1081) ∨ (¬ p883) ∨ p3 ∨ p980 ∨ (¬ p207) ∨ (¬ p227) ∨ (¬ p67) ∨ (¬ p1306) ∨ p18 ∨ (¬ p161) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p883 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u12 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h18030 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u12)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u11)
  · exact False.elim (q8 u0)
  · exact False.elim (q9 u7)

theorem step29674 (p8 p11 p63 p576 p581 p897 p1055 p1081 p1443 : Prop)
    (h26879 : p581 ∨ p576)
    (h26935 : p1443 ∨ p11)
    (h18587 : (¬ p8) ∨ (¬ p63) ∨ (¬ p581) ∨ (¬ p897) ∨ (¬ p1055) ∨ (¬ p1081) ∨ (¬ p1443)) : p576 ∨ (¬ p1055) ∨ (¬ p8) ∨ p11 ∨ (¬ p897) ∨ (¬ p63) ∨ (¬ p1081) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p576) := fun hu => hn (Or.inl hu)
  have u1 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18587 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u8)

theorem step29675 (p12 p14 p47 p125 p189 p227 p229 p420 p601 p1036 p1081 : Prop)
    (h26849 : p229 ∨ p14)
    (h26907 : p1036 ∨ p12)
    (h26881 : p601 ∨ p420)
    (h19839 : (¬ p47) ∨ (¬ p125) ∨ (¬ p189) ∨ (¬ p227) ∨ (¬ p229) ∨ (¬ p601) ∨ (¬ p1036) ∨ (¬ p1081)) : (¬ p125) ∨ p14 ∨ (¬ p47) ∨ (¬ p227) ∨ p12 ∨ (¬ p189) ∨ p420 ∨ (¬ p1081) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p14) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19839 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u7)

theorem step29676 (p3 p11 p17 p194 p226 p256 p980 p983 p1037 p1081 p1443 p1465 : Prop)
    (h26935 : p1443 ∨ p11)
    (h26903 : p983 ∨ p980)
    (h26847 : p226 ∨ p3)
    (h26853 : p256 ∨ p17)
    (h19762 : (¬ p194) ∨ (¬ p226) ∨ (¬ p256) ∨ (¬ p983) ∨ (¬ p1037) ∨ (¬ p1081) ∨ (¬ p1443) ∨ (¬ p1465)) : (¬ p1037) ∨ (¬ p1465) ∨ (¬ p194) ∨ (¬ p1081) ∨ p11 ∨ p980 ∨ p3 ∨ p17 := by
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
  have u2 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h19762 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u1)

theorem step29677 (p8 p11 p17 p86 p256 p710 p897 p904 p1074 p1081 p1097 p1443 : Prop)
    (h26853 : p256 ∨ p17)
    (h26935 : p1443 ∨ p11)
    (h26889 : p710 ∨ p8)
    (h26899 : p904 ∨ p897)
    (h18834 : (¬ p86) ∨ (¬ p256) ∨ (¬ p710) ∨ (¬ p904) ∨ (¬ p1074) ∨ (¬ p1081) ∨ (¬ p1097) ∨ (¬ p1443)) : (¬ p1074) ∨ p17 ∨ (¬ p1081) ∨ p11 ∨ p8 ∨ p897 ∨ (¬ p1097) ∨ (¬ p86) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1097 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18834 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u9)

theorem step29679 (p11 p17 p86 p161 p256 p980 p983 p1081 p1229 p1232 p1443 : Prop)
    (h26903 : p983 ∨ p980)
    (h26927 : p1232 ∨ p1229)
    (h26935 : p1443 ∨ p11)
    (h26853 : p256 ∨ p17)
    (h20376 : (¬ p86) ∨ (¬ p161) ∨ (¬ p256) ∨ (¬ p983) ∨ (¬ p1081) ∨ (¬ p1232) ∨ (¬ p1443)) : p980 ∨ (¬ p161) ∨ p1229 ∨ p11 ∨ p17 ∨ (¬ p1081) ∨ (¬ p86) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20376 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u9)

theorem step29680 (p12 p88 p161 p163 p167 p189 p532 p1036 p1081 p1225 p1270 : Prop)
    (h26925 : p1225 ∨ p161)
    (h26907 : p1036 ∨ p12)
    (h26843 : p167 ∨ p163)
    (h18130 : (¬ p88) ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p532) ∨ (¬ p1036) ∨ (¬ p1081) ∨ (¬ p1225) ∨ (¬ p1270)) : (¬ p1270) ∨ p161 ∨ (¬ p189) ∨ p12 ∨ p163 ∨ (¬ p88) ∨ (¬ p1081) ∨ (¬ p532) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1270 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p161) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18130 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u0)

theorem step29681 (p16 p125 p185 p362 p420 p455 p498 p1081 p1115 : Prop)
    (h26865 : p362 ∨ p125)
    (h19387 : (¬ p16) ∨ (¬ p185) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p455) ∨ (¬ p498) ∨ (¬ p1081) ∨ (¬ p1115)) : (¬ p420) ∨ (¬ p1115) ∨ (¬ p16) ∨ (¬ p455) ∨ p125 ∨ (¬ p498) ∨ (¬ p185) ∨ (¬ p1081) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19387 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u1)

theorem step29682 (p11 p125 p126 p301 p362 p496 p1074 p1081 p1096 p1099 p1443 : Prop)
    (h26857 : p301 ∨ p126)
    (h26865 : p362 ∨ p125)
    (h26935 : p1443 ∨ p11)
    (h26913 : p1099 ∨ p1096)
    (h16981 : (¬ p301) ∨ (¬ p362) ∨ (¬ p496) ∨ (¬ p1074) ∨ (¬ p1081) ∨ (¬ p1099) ∨ (¬ p1443)) : p126 ∨ p125 ∨ p11 ∨ p1096 ∨ (¬ p496) ∨ (¬ p1074) ∨ (¬ p1081) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p125) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16981 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u9)

theorem step29683 (p8 p664 p980 p983 p1056 p1226 : Prop)
    (h26903 : p983 ∨ p980)
    (h18378 : (¬ p8) ∨ (¬ p664) ∨ (¬ p983) ∨ (¬ p1056) ∨ (¬ p1226)) : (¬ p1226) ∨ (¬ p8) ∨ p980 ∨ (¬ p664) ∨ (¬ p1056) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1056 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18378 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u0)

theorem step29685 (p11 p17 p171 p189 p241 p256 p980 p983 p1056 p1081 p1226 p1443 : Prop)
    (h26903 : p983 ∨ p980)
    (h26853 : p256 ∨ p17)
    (h26935 : p1443 ∨ p11)
    (h20427 : (¬ p171) ∨ (¬ p189) ∨ (¬ p241) ∨ (¬ p256) ∨ (¬ p983) ∨ (¬ p1056) ∨ (¬ p1081) ∨ (¬ p1226) ∨ (¬ p1443)) : (¬ p171) ∨ p980 ∨ (¬ p1226) ∨ (¬ p241) ∨ (¬ p1081) ∨ (¬ p1056) ∨ p17 ∨ p11 ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p171 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1056 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h20427 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u2)
  · exact False.elim (q8 u11)

theorem step29687 (p38 p49 p63 p85 p926 p1035 p1044 p1096 p1115 p1116 p1163 p1226 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h26835 : p85 ∨ p63)
    (h16703 : (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p926) ∨ (¬ p1035) ∨ (¬ p1044) ∨ (¬ p1096) ∨ (¬ p1116) ∨ (¬ p1163) ∨ (¬ p1226)) : (¬ p1163) ∨ (¬ p1035) ∨ (¬ p38) ∨ p1115 ∨ p63 ∨ (¬ p1226) ∨ (¬ p1044) ∨ (¬ p926) ∨ (¬ p1096) ∨ (¬ p49) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1044 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p926 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16703 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u0)
  · exact False.elim (q9 u5)

theorem step29690 (p3 p226 p1042 p1140 p1159 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26846 : (¬ p3) ∨ (¬ p226))
    (h11360 : p226 ∨ (¬ p1042) ∨ (¬ p1159)) : (¬ p1042) ∨ p1140 ∨ (¬ p3) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1042 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1140) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u4 : (¬ p226) := by
    rcases h26846 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h11360 with q0 | q1 | q2
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)

theorem step29692 (p14 p423 p1042 p1141 : Prop)
    (h26917 : p1141 ∨ p423)
    (h12006 : (¬ p14) ∨ (¬ p1042) ∨ (¬ p1141)) : p423 ∨ (¬ p1042) ∨ (¬ p14) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p1042 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h12006 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)

theorem step29693 (p163 p422 p1042 p1256 : Prop)
    (h26928 : (¬ p422) ∨ (¬ p1256))
    (h12236 : (¬ p163) ∨ (¬ p1042) ∨ p1256) : (¬ p422) ∨ (¬ p1042) ∨ (¬ p163) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1042 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1256) := by
    rcases h26928 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h12236 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (u3 q2)

theorem step29694 (p15 p69 p110 p125 p126 p258 p288 p301 p362 p423 p496 p1042 p1141 : Prop)
    (h26857 : p301 ∨ p126)
    (h26833 : p69 ∨ p15)
    (h26865 : p362 ∨ p125)
    (h26855 : p288 ∨ p258)
    (h26917 : p1141 ∨ p423)
    (h17180 : (¬ p69) ∨ (¬ p110) ∨ (¬ p288) ∨ (¬ p301) ∨ (¬ p362) ∨ (¬ p496) ∨ (¬ p1042) ∨ (¬ p1141)) : p126 ∨ (¬ p110) ∨ p15 ∨ (¬ p496) ∨ p125 ∨ p258 ∨ p423 ∨ (¬ p1042) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p423) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1042 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u12 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h17180 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u12)

theorem step29695 (p160 p495 p633 p636 p1040 p1076 p1233 p1465 : Prop)
    (h26885 : p636 ∨ p633)
    (h18377 : (¬ p160) ∨ (¬ p495) ∨ (¬ p636) ∨ (¬ p1040) ∨ (¬ p1076) ∨ (¬ p1233) ∨ (¬ p1465)) : p633 ∨ (¬ p495) ∨ (¬ p160) ∨ (¬ p1233) ∨ (¬ p1465) ∨ (¬ p1076) ∨ (¬ p1040) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1233 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1040 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h18377 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)

theorem step29696 (p41 p63 p422 p980 p983 p1040 p1226 p1237 p1256 : Prop)
    (h26903 : p983 ∨ p980)
    (h26929 : p1256 ∨ p422)
    (h18806 : (¬ p41) ∨ (¬ p63) ∨ (¬ p983) ∨ (¬ p1040) ∨ (¬ p1226) ∨ (¬ p1237) ∨ (¬ p1256)) : p980 ∨ (¬ p1226) ∨ p422 ∨ (¬ p1237) ∨ (¬ p63) ∨ (¬ p41) ∨ (¬ p1040) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1040 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18806 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u8)

theorem step29697 (p2 p63 p85 p234 p918 p1040 p1115 p1140 : Prop)
    (h26835 : p85 ∨ p63)
    (h20197 : (¬ p2) ∨ (¬ p85) ∨ (¬ p234) ∨ (¬ p918) ∨ (¬ p1040) ∨ (¬ p1115) ∨ (¬ p1140)) : (¬ p2) ∨ (¬ p1140) ∨ p63 ∨ (¬ p1040) ∨ (¬ p234) ∨ (¬ p1115) ∨ (¬ p918) := by
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
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1040 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20197 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u1)

theorem step29698 (p17 p135 p160 p185 p256 p1040 p1115 p1250 p1348 p1465 : Prop)
    (h26853 : p256 ∨ p17)
    (h19351 : (¬ p135) ∨ (¬ p160) ∨ (¬ p185) ∨ (¬ p256) ∨ (¬ p1040) ∨ (¬ p1115) ∨ (¬ p1250) ∨ (¬ p1348) ∨ (¬ p1465)) : (¬ p1348) ∨ (¬ p1115) ∨ (¬ p1250) ∨ (¬ p1040) ∨ (¬ p1465) ∨ (¬ p185) ∨ (¬ p135) ∨ p17 ∨ (¬ p160) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1250 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1040 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h19351 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u0)
  · exact False.elim (q8 u4)

theorem step29699 (p2 p124 p186 p267 p304 p422 p424 p481 p796 p1040 p1076 p1256 : Prop)
    (h26891 : p796 ∨ p424)
    (h26859 : p304 ∨ p124)
    (h26873 : p481 ∨ p2)
    (h26929 : p1256 ∨ p422)
    (h20279 : (¬ p186) ∨ (¬ p267) ∨ (¬ p304) ∨ (¬ p481) ∨ (¬ p796) ∨ (¬ p1040) ∨ (¬ p1076) ∨ (¬ p1256)) : p424 ∨ (¬ p186) ∨ p124 ∨ p2 ∨ (¬ p1040) ∨ (¬ p1076) ∨ p422 ∨ (¬ p267) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1040 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p267 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20279 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u11)

theorem step29700 (p2 p161 p234 p980 p983 p1040 p1140 p1229 p1232 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h26903 : p983 ∨ p980)
    (h20253 : (¬ p2) ∨ (¬ p161) ∨ (¬ p234) ∨ (¬ p983) ∨ (¬ p1040) ∨ (¬ p1140) ∨ (¬ p1232)) : (¬ p2) ∨ (¬ p1140) ∨ p1229 ∨ (¬ p161) ∨ (¬ p1040) ∨ (¬ p234) ∨ p980 := by
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
  have u2 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1040 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20253 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step29702 (p63 p789 p1004 p1035 p1226 p1237 p1385 p1393 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h20606 : (¬ p63) ∨ (¬ p789) ∨ (¬ p1004) ∨ (¬ p1035) ∨ (¬ p1226) ∨ (¬ p1237) ∨ (¬ p1393)) : (¬ p1035) ∨ (¬ p789) ∨ (¬ p1004) ∨ p1385 ∨ (¬ p1237) ∨ (¬ p1226) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1035 := by
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
  have u3 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20606 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u7)

theorem step29703 (p15 p69 p227 p423 p496 p1004 p1141 p1325 p1452 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26833 : p69 ∨ p15)
    (h17162 : (¬ p69) ∨ (¬ p227) ∨ (¬ p496) ∨ (¬ p1004) ∨ (¬ p1141) ∨ (¬ p1325) ∨ (¬ p1452)) : (¬ p1004) ∨ p423 ∨ (¬ p1452) ∨ (¬ p496) ∨ (¬ p1325) ∨ (¬ p227) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p423) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h17162 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u2)

theorem step29704 (p3 p14 p83 p160 p188 p226 p423 p1004 p1141 p1233 p1325 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26847 : p226 ∨ p3)
    (h19955 : (¬ p14) ∨ (¬ p83) ∨ (¬ p160) ∨ (¬ p188) ∨ (¬ p226) ∨ (¬ p1004) ∨ (¬ p1141) ∨ (¬ p1233) ∨ (¬ p1325)) : p423 ∨ (¬ p1004) ∨ (¬ p14) ∨ (¬ p1233) ∨ (¬ p1325) ∨ p3 ∨ (¬ p160) ∨ (¬ p188) ∨ (¬ p83) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1233 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19955 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u3)
  · exact False.elim (q8 u4)

theorem step29705 (p15 p17 p69 p86 p126 p256 p303 p387 p423 p1004 p1141 : Prop)
    (h26867 : p387 ∨ p303)
    (h26853 : p256 ∨ p17)
    (h26833 : p69 ∨ p15)
    (h26917 : p1141 ∨ p423)
    (h17190 : (¬ p69) ∨ (¬ p86) ∨ (¬ p126) ∨ (¬ p256) ∨ (¬ p387) ∨ (¬ p1004) ∨ (¬ p1141)) : (¬ p1004) ∨ p303 ∨ p17 ∨ (¬ p126) ∨ (¬ p86) ∨ p15 ∨ p423 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p423) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h17190 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u10)

theorem step29706 (p3 p14 p64 p86 p226 p423 p789 p790 p1004 p1141 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26847 : p226 ∨ p3)
    (h20312 : (¬ p14) ∨ (¬ p64) ∨ (¬ p86) ∨ (¬ p226) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1004) ∨ (¬ p1141)) : p423 ∨ (¬ p1004) ∨ (¬ p14) ∨ (¬ p64) ∨ p3 ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p86) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20312 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u8)

theorem step29707 (p15 p69 p86 p185 p224 p237 p423 p657 p836 p840 p1004 p1141 : Prop)
    (h26851 : p237 ∨ p185)
    (h26833 : p69 ∨ p15)
    (h26887 : p657 ∨ p224)
    (h26895 : p840 ∨ p836)
    (h26917 : p1141 ∨ p423)
    (h20550 : (¬ p69) ∨ (¬ p86) ∨ (¬ p237) ∨ (¬ p657) ∨ (¬ p840) ∨ (¬ p1004) ∨ (¬ p1141)) : (¬ p1004) ∨ p185 ∨ p15 ∨ p224 ∨ p836 ∨ (¬ p86) ∨ p423 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p423) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20550 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u11)

theorem step29708 (p16 p189 p224 p422 p657 p897 p904 p1004 p1096 : Prop)
    (h26887 : p657 ∨ p224)
    (h26899 : p904 ∨ p897)
    (h18444 : (¬ p16) ∨ (¬ p189) ∨ (¬ p422) ∨ (¬ p657) ∨ (¬ p904) ∨ (¬ p1004) ∨ (¬ p1096)) : (¬ p422) ∨ (¬ p1004) ∨ p224 ∨ (¬ p16) ∨ (¬ p189) ∨ p897 ∨ (¬ p1096) := by
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
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18444 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u6)

theorem step29709 (p3 p16 p163 p188 p226 p422 p595 p1004 p1286 : Prop)
    (h26847 : p226 ∨ p3)
    (h19963 : (¬ p16) ∨ (¬ p163) ∨ (¬ p188) ∨ (¬ p226) ∨ (¬ p422) ∨ (¬ p595) ∨ (¬ p1004) ∨ (¬ p1286)) : (¬ p422) ∨ (¬ p1286) ∨ (¬ p188) ∨ (¬ p595) ∨ (¬ p163) ∨ (¬ p1004) ∨ p3 ∨ (¬ p16) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19963 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u1)

theorem step29710 (p15 p69 p124 p224 p344 p423 p496 p657 p1004 p1141 : Prop)
    (h26833 : p69 ∨ p15)
    (h26887 : p657 ∨ p224)
    (h26917 : p1141 ∨ p423)
    (h17091 : (¬ p69) ∨ (¬ p124) ∨ (¬ p344) ∨ (¬ p496) ∨ (¬ p657) ∨ (¬ p1004) ∨ (¬ p1141)) : (¬ p1004) ∨ (¬ p124) ∨ (¬ p496) ∨ p15 ∨ p224 ∨ (¬ p344) ∨ p423 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1004 := by
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
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p423) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h17091 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u9)

theorem step29711 (p3 p14 p64 p125 p226 p303 p362 p387 p423 p496 p1004 p1141 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26847 : p226 ∨ p3)
    (h26865 : p362 ∨ p125)
    (h26867 : p387 ∨ p303)
    (h19495 : (¬ p14) ∨ (¬ p64) ∨ (¬ p226) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p496) ∨ (¬ p1004) ∨ (¬ p1141)) : p423 ∨ p3 ∨ p125 ∨ (¬ p496) ∨ p303 ∨ (¬ p64) ∨ (¬ p1004) ∨ (¬ p14) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19495 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u8)

theorem step29738 (p2 p481 p1002 p1140 p1159 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26873 : p481 ∨ p2)
    (h11244 : (¬ p481) ∨ (¬ p1002) ∨ (¬ p1159)) : (¬ p1002) ∨ p1140 ∨ p2 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1002 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1140) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p2) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u4 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h11244 with q0 | q1 | q2
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)

theorem step29739 (p234 p423 p1002 p1141 : Prop)
    (h26917 : p1141 ∨ p423)
    (h11273 : (¬ p234) ∨ (¬ p1002) ∨ (¬ p1141)) : p423 ∨ (¬ p1002) ∨ (¬ p234) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p1002 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h11273 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)

theorem step29741 (p422 p424 p1002 p1256 : Prop)
    (h26928 : (¬ p422) ∨ (¬ p1256))
    (h14923 : (¬ p424) ∨ (¬ p1002) ∨ p1256) : (¬ p1002) ∨ (¬ p422) ∨ (¬ p424) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1002 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1256) := by
    rcases h26928 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h14923 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (u3 q2)

theorem step29742 (p422 p424 p796 p1002 : Prop)
    (h26890 : (¬ p424) ∨ (¬ p796))
    (h14772 : (¬ p422) ∨ p796 ∨ (¬ p1002)) : (¬ p1002) ∨ (¬ p422) ∨ (¬ p424) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1002 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p422 := by
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
  rcases h14772 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u0)

theorem step29743 (p2 p68 p423 p481 p1002 p1141 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26873 : p481 ∨ p2)
    (h11249 : (¬ p68) ∨ (¬ p481) ∨ (¬ p1002) ∨ (¬ p1141)) : (¬ p1002) ∨ p423 ∨ p2 ∨ (¬ p68) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1002 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p423) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h11249 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)

theorem step29744 (p789 p800 p858 p1002 p1035 p1325 : Prop)
    (h26897 : p858 ∨ p789)
    (h20651 : (¬ p800) ∨ (¬ p858) ∨ (¬ p1002) ∨ (¬ p1035) ∨ (¬ p1325)) : (¬ p800) ∨ (¬ p1035) ∨ (¬ p1002) ∨ (¬ p1325) ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p800 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1002 := by
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
  rcases h20651 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)

theorem step29745 (p3 p67 p226 p234 p883 p1002 p1035 p1074 p1325 : Prop)
    (h26847 : p226 ∨ p3)
    (h25933 : (¬ p1002) ∨ (¬ p1035) ∨ (¬ p883) ∨ (¬ p234) ∨ (¬ p1074) ∨ (¬ p1325) ∨ (¬ p226) ∨ (¬ p67)) : (¬ p1035) ∨ (¬ p1002) ∨ (¬ p1325) ∨ (¬ p234) ∨ (¬ p67) ∨ p3 ∨ (¬ p883) ∨ (¬ p1074) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1002 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p883 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h25933 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u4)

theorem step29748 (p125 p189 p224 p263 p303 p362 p387 p422 p545 p1002 : Prop)
    (h26867 : p387 ∨ p303)
    (h26865 : p362 ∨ p125)
    (h19514 : (¬ p189) ∨ (¬ p224) ∨ (¬ p263) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p422) ∨ (¬ p545) ∨ (¬ p1002)) : (¬ p1002) ∨ p303 ∨ (¬ p189) ∨ (¬ p422) ∨ (¬ p545) ∨ (¬ p224) ∨ (¬ p263) ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1002 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p263 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h19514 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u0)

theorem step29749 (p41 p63 p125 p303 p422 p1000 p1256 : Prop)
    (h26929 : p1256 ∨ p422)
    (h25935 : (¬ p41) ∨ (¬ p125) ∨ (¬ p1256) ∨ (¬ p1000) ∨ (¬ p63) ∨ (¬ p303)) : (¬ p125) ∨ p422 ∨ (¬ p63) ∨ (¬ p41) ∨ (¬ p303) ∨ (¬ p1000) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p422) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p41 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h25935 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u4)

theorem step29750 (p124 p189 p193 p224 p267 p304 p344 p346 p422 p1000 p1256 : Prop)
    (h26929 : p1256 ∨ p422)
    (h26859 : p304 ∨ p124)
    (h26863 : p346 ∨ p344)
    (h26845 : p193 ∨ p189)
    (h18845 : (¬ p193) ∨ (¬ p224) ∨ (¬ p267) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p1000) ∨ (¬ p1256)) : p422 ∨ p124 ∨ p344 ∨ (¬ p1000) ∨ (¬ p224) ∨ (¬ p267) ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p422) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p267 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18845 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step29751 (p234 p423 p424 p796 p998 p1141 p1325 : Prop)
    (h26891 : p796 ∨ p424)
    (h26917 : p1141 ∨ p423)
    (h16837 : (¬ p234) ∨ (¬ p796) ∨ (¬ p998) ∨ (¬ p1141) ∨ (¬ p1325)) : (¬ p998) ∨ p424 ∨ (¬ p234) ∨ p423 ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p998 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p424) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p423) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16837 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u4)

theorem step29752 (p234 p423 p998 p1141 p1366 : Prop)
    (h26917 : p1141 ∨ p423)
    (h25936 : (¬ p1366) ∨ (¬ p234) ∨ (¬ p998) ∨ (¬ p1141)) : (¬ p1366) ∨ (¬ p998) ∨ (¬ p234) ∨ p423 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p998 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p423) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h25936 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)

theorem step29756 (p2 p224 p481 p542 p657 p998 p1140 p1159 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26887 : p657 ∨ p224)
    (h26873 : p481 ∨ p2)
    (h19902 : (¬ p481) ∨ (¬ p542) ∨ (¬ p657) ∨ (¬ p998) ∨ (¬ p1159)) : (¬ p998) ∨ p1140 ∨ p224 ∨ (¬ p542) ∨ p2 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p998 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1140) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19902 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)

theorem step29757 (p327 p419 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h20223 : p327 ∨ (¬ p996)) : p327 ∨ p419 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p327) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p419) := fun hu => hn (Or.inr hu)
  have u2 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20223 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)

theorem step29758 (p419 p435 p996 p1332 : Prop)
    (h26905 : p996 ∨ p419)
    (h11138 : (¬ p435) ∨ (¬ p996) ∨ (¬ p1332)) : p419 ∨ (¬ p1332) ∨ (¬ p435) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : p1332 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h11138 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)

theorem step29760 (p419 p996 p1192 p1286 : Prop)
    (h26905 : p996 ∨ p419)
    (h15964 : (¬ p996) ∨ (¬ p1192) ∨ p1286) : p419 ∨ p1286 ∨ (¬ p1192) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1286) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h15964 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)

theorem step29761 (p63 p419 p435 p996 p1229 p1232 p1295 p1389 p1542 : Prop)
    (h26905 : p996 ∨ p419)
    (h26927 : p1232 ∨ p1229)
    (h20475 : (¬ p63) ∨ (¬ p435) ∨ (¬ p996) ∨ (¬ p1232) ∨ (¬ p1295) ∨ (¬ p1389) ∨ (¬ p1542)) : (¬ p1389) ∨ (¬ p1295) ∨ p419 ∨ (¬ p435) ∨ (¬ p1542) ∨ p1229 ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1295 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20475 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u4)

theorem step29762 (p419 p435 p790 p996 p1022 : Prop)
    (h26905 : p996 ∨ p419)
    (h17424 : (¬ p435) ∨ (¬ p790) ∨ (¬ p996) ∨ (¬ p1022)) : (¬ p1022) ∨ (¬ p790) ∨ (¬ p435) ∨ p419 := by
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
  have u2 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17424 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step29763 (p419 p790 p800 p857 p996 p1349 : Prop)
    (h26905 : p996 ∨ p419)
    (h17921 : (¬ p790) ∨ (¬ p800) ∨ (¬ p857) ∨ (¬ p996) ∨ (¬ p1349)) : (¬ p800) ∨ (¬ p1349) ∨ p419 ∨ (¬ p790) ∨ (¬ p857) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p800 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p857 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17921 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)

theorem step29764 (p15 p234 p419 p996 p1325 p1333 : Prop)
    (h26905 : p996 ∨ p419)
    (h26931 : p1333 ∨ p1325)
    (h19625 : (¬ p15) ∨ (¬ p234) ∨ (¬ p996) ∨ (¬ p1333)) : p419 ∨ p1325 ∨ (¬ p15) ∨ (¬ p234) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p15 := by
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
  have u5 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19625 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

#print axioms step29764

end NineRUPTrial
