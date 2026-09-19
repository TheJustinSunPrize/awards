import Mathlib.Tactic.Tauto

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

namespace NineRUPTrial

theorem step17925 (p6 p7 p45 p140 p191 p581 : Prop)
    (h16152 : (¬ p7))
    (h13046 : (¬ p6) ∨ p7 ∨ (¬ p45) ∨ (¬ p140) ∨ (¬ p191) ∨ (¬ p581)) : (¬ p6) ∨ (¬ p45) ∨ (¬ p140) ∨ (¬ p191) ∨ (¬ p581) := by
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
  have u2 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13046 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17926 (p7 p796 p1001 p1191 p1256 p1287 : Prop)
    (h16152 : (¬ p7))
    (h13047 : p7 ∨ (¬ p796) ∨ (¬ p1001) ∨ (¬ p1191) ∨ (¬ p1256) ∨ (¬ p1287)) : (¬ p796) ∨ (¬ p1001) ∨ (¬ p1191) ∨ (¬ p1256) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1001 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13047 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17927 (p7 p167 p189 p279 p980 p1036 p1324 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16309 : (¬ p1324))
    (h13048 : p7 ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p279) ∨ (¬ p980) ∨ (¬ p1036) ∨ p1324) : (¬ p167) ∨ (¬ p189) ∨ (¬ p980) ∨ (¬ p1036) := by
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
  have u2 : p980 := by
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
  have u6 : (¬ p1324) := by
    exact h16309
  rcases h13048 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step17928 (p7 p667 p901 p983 p1287 p1325 : Prop)
    (h16152 : (¬ p7))
    (h13049 : p7 ∨ (¬ p667) ∨ (¬ p901) ∨ (¬ p983) ∨ (¬ p1287) ∨ (¬ p1325)) : (¬ p667) ∨ (¬ p901) ∨ (¬ p983) ∨ (¬ p1287) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p667 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p901 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p983 := by
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
  rcases h13049 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17929 (p7 p400 p479 p996 p1226 p1333 : Prop)
    (h16152 : (¬ p7))
    (h13050 : p7 ∨ (¬ p400) ∨ (¬ p479) ∨ (¬ p996) ∨ (¬ p1226) ∨ (¬ p1333)) : (¬ p400) ∨ (¬ p479) ∨ (¬ p996) ∨ (¬ p1226) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p400 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p479 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13050 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17930 (p7 p101 p134 p189 p279 p346 p426 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16178 : (¬ p426))
    (h13051 : p7 ∨ (¬ p101) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p279) ∨ (¬ p346) ∨ p426) : (¬ p101) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p346) := by
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
  have u3 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p279 := by
    exact h1444
  have u6 : (¬ p426) := by
    exact h16178
  rcases h13051 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step17932 (p16 p83 p85 p230 p1184 : Prop)
    (h16165 : (¬ p230))
    (h7053 : p1184)
    (h13053 : p16 ∨ (¬ p83) ∨ (¬ p85) ∨ p230 ∨ (¬ p1184)) : p16 ∨ (¬ p83) ∨ (¬ p85) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p16) := fun hu => hn (Or.inl hu)
  have u1 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p230) := by
    exact h16165
  have u4 : p1184 := by
    exact h7053
  rcases h13053 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)

theorem step17933 (p7 p16 p17 p258 p726 p985 p1225 p1229 : Prop)
    (h16152 : (¬ p7))
    (h13054 : p7 ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p258) ∨ (¬ p726) ∨ (¬ p985) ∨ (¬ p1225) ∨ (¬ p1229)) : (¬ p16) ∨ (¬ p17) ∨ (¬ p258) ∨ (¬ p726) ∨ (¬ p985) ∨ (¬ p1225) ∨ (¬ p1229) := by
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
  have u3 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p985 := by
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
  rcases h13054 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17934 (p7 p160 p161 p401 p996 p1191 p1288 : Prop)
    (h16152 : (¬ p7))
    (h13055 : p7 ∨ (¬ p160) ∨ (¬ p161) ∨ (¬ p401) ∨ (¬ p996) ∨ (¬ p1191) ∨ (¬ p1288)) : (¬ p160) ∨ (¬ p161) ∨ (¬ p401) ∨ (¬ p996) ∨ (¬ p1191) ∨ (¬ p1288) := by
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
  have u2 : p401 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h13055 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17935 (p7 p16 p167 p189 p940 p985 p1225 p1229 : Prop)
    (h16152 : (¬ p7))
    (h13056 : p7 ∨ (¬ p16) ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1225) ∨ (¬ p1229)) : (¬ p16) ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1225) ∨ (¬ p1229) := by
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
  have u3 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p985 := by
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
  rcases h13056 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17936 (p7 p165 p189 p279 p426 p534 p667 p1036 p1584 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16178 : (¬ p426))
    (h13057 : p7 ∨ (¬ p165) ∨ (¬ p189) ∨ (¬ p279) ∨ p426 ∨ (¬ p534) ∨ (¬ p667) ∨ (¬ p1036) ∨ (¬ p1584)) : (¬ p165) ∨ (¬ p189) ∨ (¬ p534) ∨ (¬ p667) ∨ (¬ p1036) ∨ (¬ p1584) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p165 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p667 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : p279 := by
    exact h1444
  have u8 : (¬ p426) := by
    exact h16178
  rcases h13057 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u7)
  · exact False.elim (u8 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)

theorem step17937 (p7 p8 p142 p167 p225 p682 p788 : Prop)
    (h16152 : (¬ p7))
    (h16203 : (¬ p682))
    (h5066 : p788)
    (h13058 : p7 ∨ (¬ p8) ∨ (¬ p142) ∨ (¬ p167) ∨ (¬ p225) ∨ p682 ∨ (¬ p788)) : (¬ p8) ∨ (¬ p142) ∨ (¬ p167) ∨ (¬ p225) := by
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
  have u5 : (¬ p682) := by
    exact h16203
  have u6 : p788 := by
    exact h5066
  rcases h13058 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)

theorem step17938 (p1 p7 p382 p713 p882 p897 p996 : Prop)
    (h16152 : (¬ p7))
    (h13060 : (¬ p1) ∨ p7 ∨ (¬ p382) ∨ (¬ p713) ∨ (¬ p882) ∨ (¬ p897) ∨ (¬ p996)) : (¬ p1) ∨ (¬ p382) ∨ (¬ p713) ∨ (¬ p882) ∨ (¬ p897) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p713 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h13060 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17940 (p6 p7 p10 p601 p636 p659 p686 : Prop)
    (h16152 : (¬ p7))
    (h3753 : p659)
    (h16205 : (¬ p686))
    (h13062 : (¬ p6) ∨ p7 ∨ (¬ p10) ∨ (¬ p601) ∨ (¬ p636) ∨ (¬ p659) ∨ p686) : (¬ p6) ∨ (¬ p10) ∨ (¬ p601) ∨ (¬ p636) := by
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
  have u5 : p659 := by
    exact h3753
  have u6 : (¬ p686) := by
    exact h16205
  rcases h13062 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)

theorem step17941 (p7 p167 p189 p225 p279 p430 p734 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16180 : (¬ p430))
    (h13063 : p7 ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p225) ∨ (¬ p279) ∨ p430 ∨ (¬ p734)) : (¬ p167) ∨ (¬ p189) ∨ (¬ p225) ∨ (¬ p734) := by
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
  have u3 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p279 := by
    exact h1444
  have u6 : (¬ p430) := by
    exact h16180
  rcases h13063 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step17942 (p7 p382 p423 p479 p1001 p1187 : Prop)
    (h16152 : (¬ p7))
    (h13064 : p7 ∨ (¬ p382) ∨ (¬ p423) ∨ (¬ p479) ∨ (¬ p1001) ∨ (¬ p1187)) : (¬ p382) ∨ (¬ p423) ∨ (¬ p479) ∨ (¬ p1001) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p479 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1001 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13064 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17943 (p7 p14 p42 p167 p1141 p1324 p1465 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16309 : (¬ p1324))
    (h13065 : p7 ∨ (¬ p14) ∨ (¬ p42) ∨ (¬ p167) ∨ (¬ p1141) ∨ p1324 ∨ (¬ p1465)) : (¬ p14) ∨ (¬ p167) ∨ (¬ p1141) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p167 := by
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
  have u5 : p42 := by
    exact h132
  have u6 : (¬ p1324) := by
    exact h16309
  rcases h13065 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step17944 (p7 p69 p225 p229 p430 p734 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16180 : (¬ p430))
    (h7053 : p1184)
    (h13066 : p7 ∨ (¬ p69) ∨ (¬ p225) ∨ (¬ p229) ∨ p430 ∨ (¬ p734) ∨ (¬ p1184)) : (¬ p69) ∨ (¬ p225) ∨ (¬ p229) ∨ (¬ p734) := by
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
  have u3 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p430) := by
    exact h16180
  have u6 : p1184 := by
    exact h7053
  rcases h13066 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step17945 (p7 p17 p42 p193 p309 p382 p430 p540 p709 p734 p752 p996 p1644 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16180 : (¬ p430))
    (h13067 : p7 ∨ (¬ p17) ∨ (¬ p42) ∨ (¬ p193) ∨ (¬ p309) ∨ (¬ p382) ∨ p430 ∨ (¬ p540) ∨ (¬ p709) ∨ (¬ p734) ∨ (¬ p752) ∨ (¬ p996) ∨ (¬ p1644)) : (¬ p17) ∨ (¬ p193) ∨ (¬ p309) ∨ (¬ p382) ∨ (¬ p540) ∨ (¬ p709) ∨ (¬ p734) ∨ (¬ p752) ∨ (¬ p996) ∨ (¬ p1644) := by
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
  have u2 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p540 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p709 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p752 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1644 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  have u11 : p42 := by
    exact h132
  have u12 : (¬ p430) := by
    exact h16180
  rcases h13067 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  · exact False.elim (u10 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u12 q6)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)
  · exact False.elim (q12 u9)

theorem step17946 (p7 p41 p138 p575 p1604 p1651 : Prop)
    (h16152 : (¬ p7))
    (h13068 : p7 ∨ (¬ p41) ∨ (¬ p138) ∨ (¬ p575) ∨ (¬ p1604) ∨ (¬ p1651)) : (¬ p41) ∨ (¬ p138) ∨ (¬ p575) ∨ (¬ p1604) ∨ (¬ p1651) := by
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
  have u2 : p575 := by
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
  rcases h13068 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17947 (p5 p7 p382 p440 p499 p540 p556 p709 p734 p996 p1611 : Prop)
    (h16152 : (¬ p7))
    (h13070 : (¬ p5) ∨ p7 ∨ (¬ p382) ∨ (¬ p440) ∨ (¬ p499) ∨ (¬ p540) ∨ (¬ p556) ∨ (¬ p709) ∨ (¬ p734) ∨ (¬ p996) ∨ (¬ p1611)) : (¬ p5) ∨ (¬ p382) ∨ (¬ p440) ∨ (¬ p499) ∨ (¬ p540) ∨ (¬ p556) ∨ (¬ p709) ∨ (¬ p734) ∨ (¬ p996) ∨ (¬ p1611) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p440 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p540 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p556 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p709 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1611 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h13070 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step17948 (p7 p139 p301 p303 p329 p996 : Prop)
    (h16152 : (¬ p7))
    (h13073 : p7 ∨ (¬ p139) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p329) ∨ (¬ p996)) : (¬ p139) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p329) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p139 := by
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
  have u3 : p329 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13073 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17949 (p7 p132 p189 p256 p422 p1324 p1465 : Prop)
    (h16152 : (¬ p7))
    (h786 : p132)
    (h16309 : (¬ p1324))
    (h13075 : p7 ∨ (¬ p132) ∨ (¬ p189) ∨ (¬ p256) ∨ (¬ p422) ∨ p1324 ∨ (¬ p1465)) : (¬ p189) ∨ (¬ p256) ∨ (¬ p422) ∨ (¬ p1465) := by
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
  have u2 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p132 := by
    exact h786
  have u6 : (¬ p1324) := by
    exact h16309
  rcases h13075 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step17950 (p7 p41 p42 p382 p819 p1324 p1325 p1385 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16309 : (¬ p1324))
    (h13076 : p7 ∨ (¬ p41) ∨ (¬ p42) ∨ (¬ p382) ∨ (¬ p819) ∨ p1324 ∨ (¬ p1325) ∨ (¬ p1385)) : (¬ p41) ∨ (¬ p382) ∨ (¬ p819) ∨ (¬ p1325) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p382 := by
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
  have u6 : p42 := by
    exact h132
  have u7 : (¬ p1324) := by
    exact h16309
  rcases h13076 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u7 q5)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step17951 (p7 p185 p224 p279 p280 p387 p836 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16173 : (¬ p280))
    (h13077 : p7 ∨ (¬ p185) ∨ (¬ p224) ∨ (¬ p279) ∨ p280 ∨ (¬ p387) ∨ (¬ p836)) : (¬ p185) ∨ (¬ p224) ∨ (¬ p387) ∨ (¬ p836) := by
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
  have u2 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p279 := by
    exact h1444
  have u6 : (¬ p280) := by
    exact h16173
  rcases h13077 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17952 (p7 p224 p285 p349 p387 p836 : Prop)
    (h16152 : (¬ p7))
    (h13078 : p7 ∨ (¬ p224) ∨ (¬ p285) ∨ (¬ p349) ∨ (¬ p387) ∨ (¬ p836)) : (¬ p224) ∨ (¬ p285) ∨ (¬ p349) ∨ (¬ p387) ∨ (¬ p836) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p285 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13078 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17953 (p7 p45 p193 p302 p792 p814 p858 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h4535 : p792)
    (h13079 : p7 ∨ (¬ p45) ∨ (¬ p193) ∨ p302 ∨ (¬ p792) ∨ (¬ p814) ∨ (¬ p858)) : (¬ p45) ∨ (¬ p193) ∨ (¬ p814) ∨ (¬ p858) := by
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
  rcases h13079 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17954 (p7 p18 p63 p69 p101 p686 p792 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h4535 : p792)
    (h13082 : p7 ∨ (¬ p18) ∨ (¬ p63) ∨ (¬ p69) ∨ (¬ p101) ∨ p686 ∨ (¬ p792)) : (¬ p18) ∨ (¬ p63) ∨ (¬ p69) ∨ (¬ p101) := by
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
  have u2 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p686) := by
    exact h16205
  have u6 : p792 := by
    exact h4535
  rcases h13082 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)

theorem step17955 (p7 p21 p101 p350 p438 p600 p1542 : Prop)
    (h16152 : (¬ p7))
    (h13083 : p7 ∨ (¬ p21) ∨ (¬ p101) ∨ (¬ p350) ∨ (¬ p438) ∨ (¬ p600) ∨ (¬ p1542)) : (¬ p21) ∨ (¬ p101) ∨ (¬ p350) ∨ (¬ p438) ∨ (¬ p600) ∨ (¬ p1542) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p21 := by
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
  have u3 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p600 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h13083 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17956 (p6 p7 p101 p328 p350 p481 : Prop)
    (h16152 : (¬ p7))
    (h13084 : (¬ p6) ∨ p7 ∨ (¬ p101) ∨ (¬ p328) ∨ (¬ p350) ∨ (¬ p481)) : (¬ p6) ∨ (¬ p101) ∨ (¬ p328) ∨ (¬ p350) ∨ (¬ p481) := by
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
  have u2 : p328 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13084 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17957 (p6 p7 p14 p24 p67 p544 p636 p664 p1076 : Prop)
    (h16152 : (¬ p7))
    (h13085 : (¬ p6) ∨ p7 ∨ (¬ p14) ∨ (¬ p24) ∨ (¬ p67) ∨ (¬ p544) ∨ (¬ p636) ∨ (¬ p664) ∨ (¬ p1076)) : (¬ p6) ∨ (¬ p14) ∨ (¬ p24) ∨ (¬ p67) ∨ (¬ p544) ∨ (¬ p636) ∨ (¬ p664) ∨ (¬ p1076) := by
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
  have u2 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p636 := by
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
  rcases h13085 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17958 (p7 p305 p350 p362 p1055 p1077 : Prop)
    (h16152 : (¬ p7))
    (h13086 : p7 ∨ (¬ p305) ∨ (¬ p350) ∨ (¬ p362) ∨ (¬ p1055) ∨ (¬ p1077)) : (¬ p305) ∨ (¬ p350) ∨ (¬ p362) ∨ (¬ p1055) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p362 := by
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
  rcases h13086 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17959 (p7 p14 p50 p166 p185 p193 : Prop)
    (h16152 : (¬ p7))
    (h13087 : p7 ∨ (¬ p14) ∨ (¬ p50) ∨ (¬ p166) ∨ (¬ p185) ∨ (¬ p193)) : (¬ p14) ∨ (¬ p50) ∨ (¬ p166) ∨ (¬ p185) ∨ (¬ p193) := by
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
  rcases h13087 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17960 (p7 p230 p343 p544 p928 p1036 p1116 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h1950 : p343)
    (h13088 : p7 ∨ p230 ∨ (¬ p343) ∨ (¬ p544) ∨ (¬ p928) ∨ (¬ p1036) ∨ (¬ p1116)) : (¬ p544) ∨ (¬ p928) ∨ (¬ p1036) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p928 := by
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
  have u5 : (¬ p230) := by
    exact h16165
  have u6 : p343 := by
    exact h1950
  rcases h13088 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17961 (p7 p387 p517 p857 p1249 p1393 : Prop)
    (h16152 : (¬ p7))
    (h13089 : p7 ∨ (¬ p387) ∨ (¬ p517) ∨ (¬ p857) ∨ (¬ p1249) ∨ (¬ p1393)) : (¬ p387) ∨ (¬ p517) ∨ (¬ p857) ∨ (¬ p1249) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p517 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p857 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13089 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17964 (p7 p14 p109 p207 p368 p406 p1188 p1287 : Prop)
    (h16152 : (¬ p7))
    (h13094 : p7 ∨ (¬ p14) ∨ (¬ p109) ∨ (¬ p207) ∨ (¬ p368) ∨ (¬ p406) ∨ (¬ p1188) ∨ (¬ p1287)) : (¬ p14) ∨ (¬ p109) ∨ (¬ p207) ∨ (¬ p368) ∨ (¬ p406) ∨ (¬ p1188) ∨ (¬ p1287) := by
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
  rcases h13094 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17965 (p7 p90 p256 p519 p789 p1287 p1387 : Prop)
    (h16152 : (¬ p7))
    (h13095 : p7 ∨ (¬ p90) ∨ (¬ p256) ∨ (¬ p519) ∨ (¬ p789) ∨ (¬ p1287) ∨ (¬ p1387)) : (¬ p90) ∨ (¬ p256) ∨ (¬ p519) ∨ (¬ p789) ∨ (¬ p1287) ∨ (¬ p1387) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p90 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p519 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p789 := by
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
  rcases h13095 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17966 (p7 p63 p303 p427 p789 p1136 p1393 : Prop)
    (h16152 : (¬ p7))
    (h2334 : p427)
    (h16259 : (¬ p1136))
    (h13096 : p7 ∨ (¬ p63) ∨ (¬ p303) ∨ (¬ p427) ∨ (¬ p789) ∨ p1136 ∨ (¬ p1393)) : (¬ p63) ∨ (¬ p303) ∨ (¬ p789) ∨ (¬ p1393) := by
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
  have u5 : p427 := by
    exact h2334
  have u6 : (¬ p1136) := by
    exact h16259
  rcases h13096 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step17967 (p7 p11 p126 p370 p384 p406 : Prop)
    (h16152 : (¬ p7))
    (h13097 : p7 ∨ (¬ p11) ∨ (¬ p126) ∨ (¬ p370) ∨ (¬ p384) ∨ (¬ p406)) : (¬ p11) ∨ (¬ p126) ∨ (¬ p370) ∨ (¬ p384) ∨ (¬ p406) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p370 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p384 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13097 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17969 (p7 p63 p581 p1136 p1386 p1443 p1452 : Prop)
    (h16152 : (¬ p7))
    (h16259 : (¬ p1136))
    (h8348 : p1386)
    (h13099 : p7 ∨ (¬ p63) ∨ (¬ p581) ∨ p1136 ∨ (¬ p1386) ∨ (¬ p1443) ∨ (¬ p1452)) : (¬ p63) ∨ (¬ p581) ∨ (¬ p1443) ∨ (¬ p1452) := by
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
  have u5 : (¬ p1136) := by
    exact h16259
  have u6 : p1386 := by
    exact h8348
  rcases h13099 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17970 (p7 p63 p224 p228 p581 p710 p1103 p1443 : Prop)
    (h16152 : (¬ p7))
    (h13100 : p7 ∨ (¬ p63) ∨ (¬ p224) ∨ (¬ p228) ∨ (¬ p581) ∨ (¬ p710) ∨ (¬ p1103) ∨ (¬ p1443)) : (¬ p63) ∨ (¬ p224) ∨ (¬ p228) ∨ (¬ p581) ∨ (¬ p710) ∨ (¬ p1103) ∨ (¬ p1443) := by
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
  have u2 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13100 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17971 (p7 p331 p381 p532 p996 p1333 : Prop)
    (h16152 : (¬ p7))
    (h13103 : p7 ∨ (¬ p331) ∨ (¬ p381) ∨ (¬ p532) ∨ (¬ p996) ∨ (¬ p1333)) : (¬ p331) ∨ (¬ p381) ∨ (¬ p532) ∨ (¬ p996) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p331 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p381 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
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
  rcases h13103 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17972 (p2 p3 p7 p128 p229 p256 p576 p791 p800 p1393 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16213 : (¬ p791))
    (h13104 : (¬ p2) ∨ (¬ p3) ∨ p7 ∨ (¬ p128) ∨ (¬ p229) ∨ (¬ p256) ∨ (¬ p576) ∨ p791 ∨ (¬ p800) ∨ (¬ p1393)) : (¬ p2) ∨ (¬ p3) ∨ (¬ p229) ∨ (¬ p256) ∨ (¬ p576) ∨ (¬ p800) ∨ (¬ p1393) := by
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
  have u3 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p800 := by
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
  have u9 : (¬ p791) := by
    exact h16213
  rcases h13104 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u9 q7)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)

theorem step17973 (p5 p7 p63 p126 p225 p226 p347 p581 : Prop)
    (h16152 : (¬ p7))
    (h13106 : (¬ p5) ∨ p7 ∨ (¬ p63) ∨ (¬ p126) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p347) ∨ (¬ p581)) : (¬ p5) ∨ (¬ p63) ∨ (¬ p126) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p347) ∨ (¬ p581) := by
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
  have u2 : p126 := by
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
  have u5 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13106 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17974 (p7 p102 p127 p136 p195 p258 : Prop)
    (h16152 : (¬ p7))
    (h13107 : p7 ∨ (¬ p102) ∨ (¬ p127) ∨ (¬ p136) ∨ (¬ p195) ∨ (¬ p258)) : (¬ p102) ∨ (¬ p127) ∨ (¬ p136) ∨ (¬ p195) ∨ (¬ p258) := by
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
  have u2 : p136 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13107 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17976 (p7 p63 p382 p545 p621 p662 p928 p996 p1116 : Prop)
    (h16152 : (¬ p7))
    (h13109 : p7 ∨ (¬ p63) ∨ (¬ p382) ∨ (¬ p545) ∨ (¬ p621) ∨ (¬ p662) ∨ (¬ p928) ∨ (¬ p996) ∨ (¬ p1116)) : (¬ p63) ∨ (¬ p382) ∨ (¬ p545) ∨ (¬ p621) ∨ (¬ p662) ∨ (¬ p928) ∨ (¬ p996) ∨ (¬ p1116) := by
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
  have u2 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p621 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p662 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13109 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17977 (p2 p5 p7 p63 p419 p665 p928 p1116 : Prop)
    (h16152 : (¬ p7))
    (h13110 : (¬ p2) ∨ (¬ p5) ∨ p7 ∨ (¬ p63) ∨ (¬ p419) ∨ (¬ p665) ∨ (¬ p928) ∨ (¬ p1116)) : (¬ p2) ∨ (¬ p5) ∨ (¬ p63) ∨ (¬ p419) ∨ (¬ p665) ∨ (¬ p928) ∨ (¬ p1116) := by
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
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13110 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17978 (p7 p128 p481 p499 p633 p1044 p1077 p1136 p1159 p1187 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16259 : (¬ p1136))
    (h13113 : p7 ∨ (¬ p128) ∨ (¬ p481) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p1044) ∨ (¬ p1077) ∨ p1136 ∨ (¬ p1159) ∨ (¬ p1187)) : (¬ p481) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p1044) ∨ (¬ p1077) ∨ (¬ p1159) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p481 := by
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
  have u3 : p1044 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : p128 := by
    exact h653
  have u9 : (¬ p1136) := by
    exact h16259
  rcases h13113 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step17979 (p2 p7 p302 p435 p659 p1287 p1542 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h3753 : p659)
    (h13114 : (¬ p2) ∨ p7 ∨ p302 ∨ (¬ p435) ∨ (¬ p659) ∨ (¬ p1287) ∨ (¬ p1542)) : (¬ p2) ∨ (¬ p435) ∨ (¬ p1287) ∨ (¬ p1542) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p302) := by
    exact h16285
  have u6 : p659 := by
    exact h3753
  rcases h13114 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17981 (p6 p7 p19 p104 p229 p346 p426 p659 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h3753 : p659)
    (h13116 : (¬ p6) ∨ p7 ∨ (¬ p19) ∨ (¬ p104) ∨ (¬ p229) ∨ (¬ p346) ∨ p426 ∨ (¬ p659)) : (¬ p6) ∨ (¬ p19) ∨ (¬ p104) ∨ (¬ p229) ∨ (¬ p346) := by
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
  have u2 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p426) := by
    exact h16178
  have u7 : p659 := by
    exact h3753
  rcases h13116 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u6 q6)
  · exact False.elim (q7 u7)

theorem step17982 (p6 p7 p101 p481 p686 p996 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h6744 : p1135)
    (h13118 : (¬ p6) ∨ p7 ∨ (¬ p101) ∨ (¬ p481) ∨ p686 ∨ (¬ p996) ∨ (¬ p1135)) : (¬ p6) ∨ (¬ p101) ∨ (¬ p481) ∨ (¬ p996) := by
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
  have u5 : (¬ p686) := by
    exact h16205
  have u6 : p1135 := by
    exact h6744
  rcases h13118 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step17985 (p6 p7 p10 p25 p67 p601 : Prop)
    (h16152 : (¬ p7))
    (h13121 : (¬ p6) ∨ p7 ∨ (¬ p10) ∨ (¬ p25) ∨ (¬ p67) ∨ (¬ p601)) : (¬ p6) ∨ (¬ p10) ∨ (¬ p25) ∨ (¬ p67) ∨ (¬ p601) := by
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
  have u2 : p25 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13121 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17986 (p7 p19 p40 p102 p344 p657 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h6744 : p1135)
    (h13122 : p7 ∨ (¬ p19) ∨ p40 ∨ (¬ p102) ∨ (¬ p344) ∨ (¬ p657) ∨ (¬ p1135)) : (¬ p19) ∨ (¬ p102) ∨ (¬ p344) ∨ (¬ p657) := by
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
  have u5 : (¬ p40) := by
    exact h16150
  have u6 : p1135 := by
    exact h6744
  rcases h13122 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step17988 (p7 p14 p40 p343 p344 p534 p726 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h1950 : p343)
    (h13124 : p7 ∨ (¬ p14) ∨ p40 ∨ (¬ p343) ∨ (¬ p344) ∨ (¬ p534) ∨ (¬ p726)) : (¬ p14) ∨ (¬ p344) ∨ (¬ p534) ∨ (¬ p726) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
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
  have u5 : (¬ p40) := by
    exact h16150
  have u6 : p343 := by
    exact h1950
  rcases h13124 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17990 (p7 p19 p67 p124 p161 p207 p533 p756 p1145 p1159 : Prop)
    (h16152 : (¬ p7))
    (h13126 : p7 ∨ (¬ p19) ∨ (¬ p67) ∨ (¬ p124) ∨ (¬ p161) ∨ (¬ p207) ∨ (¬ p533) ∨ (¬ p756) ∨ (¬ p1145) ∨ (¬ p1159)) : (¬ p19) ∨ (¬ p67) ∨ (¬ p124) ∨ (¬ p161) ∨ (¬ p207) ∨ (¬ p533) ∨ (¬ p756) ∨ (¬ p1145) ∨ (¬ p1159) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1145 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h13126 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step17991 (p7 p14 p40 p346 p544 p1077 p1139 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h6761 : p1139)
    (h13127 : p7 ∨ (¬ p14) ∨ p40 ∨ (¬ p346) ∨ (¬ p544) ∨ (¬ p1077) ∨ (¬ p1139)) : (¬ p14) ∨ (¬ p346) ∨ (¬ p544) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
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
  have u5 : (¬ p40) := by
    exact h16150
  have u6 : p1139 := by
    exact h6761
  rcases h13127 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step17992 (p6 p7 p19 p64 p224 p406 p545 p617 p1187 : Prop)
    (h16152 : (¬ p7))
    (h13130 : (¬ p6) ∨ p7 ∨ (¬ p19) ∨ (¬ p64) ∨ (¬ p224) ∨ (¬ p406) ∨ (¬ p545) ∨ (¬ p617) ∨ (¬ p1187)) : (¬ p6) ∨ (¬ p19) ∨ (¬ p64) ∨ (¬ p224) ∨ (¬ p406) ∨ (¬ p545) ∨ (¬ p617) ∨ (¬ p1187) := by
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
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p617 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13130 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17993 (p6 p7 p24 p67 p234 p346 p534 p539 p636 p738 : Prop)
    (h16152 : (¬ p7))
    (h13131 : (¬ p6) ∨ p7 ∨ (¬ p24) ∨ (¬ p67) ∨ (¬ p234) ∨ (¬ p346) ∨ (¬ p534) ∨ (¬ p539) ∨ (¬ p636) ∨ (¬ p738)) : (¬ p6) ∨ (¬ p24) ∨ (¬ p67) ∨ (¬ p234) ∨ (¬ p346) ∨ (¬ p534) ∨ (¬ p539) ∨ (¬ p636) ∨ (¬ p738) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p539 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p738 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h13131 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step17994 (p7 p14 p534 p540 p738 p1187 : Prop)
    (h16152 : (¬ p7))
    (h13132 : p7 ∨ (¬ p14) ∨ (¬ p534) ∨ (¬ p540) ∨ (¬ p738) ∨ (¬ p1187)) : (¬ p14) ∨ (¬ p534) ∨ (¬ p540) ∨ (¬ p738) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p540 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p738 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13132 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17996 (p7 p19 p102 p325 p342 p1187 : Prop)
    (h16152 : (¬ p7))
    (h13135 : p7 ∨ (¬ p19) ∨ (¬ p102) ∨ (¬ p325) ∨ (¬ p342) ∨ (¬ p1187)) : (¬ p19) ∨ (¬ p102) ∨ (¬ p325) ∨ (¬ p342) ∨ (¬ p1187) := by
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
  have u2 : p325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p342 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13135 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17997 (p7 p406 p495 p617 p636 p726 p985 p1333 : Prop)
    (h16152 : (¬ p7))
    (h13136 : p7 ∨ (¬ p406) ∨ (¬ p495) ∨ (¬ p617) ∨ (¬ p636) ∨ (¬ p726) ∨ (¬ p985) ∨ (¬ p1333)) : (¬ p406) ∨ (¬ p495) ∨ (¬ p617) ∨ (¬ p636) ∨ (¬ p726) ∨ (¬ p985) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p617 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p636 := by
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
  have u6 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13136 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17998 (p7 p64 p226 p346 p426 p756 p940 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h7053 : p1184)
    (h13137 : p7 ∨ (¬ p64) ∨ (¬ p226) ∨ (¬ p346) ∨ p426 ∨ (¬ p756) ∨ (¬ p940) ∨ (¬ p1184)) : (¬ p64) ∨ (¬ p226) ∨ (¬ p346) ∨ (¬ p756) ∨ (¬ p940) := by
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
  have u2 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p426) := by
    exact h16178
  have u7 : p1184 := by
    exact h7053
  rcases h13137 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step17999 (p4 p7 p10 p102 p738 p756 : Prop)
    (h16152 : (¬ p7))
    (h13138 : (¬ p4) ∨ p7 ∨ (¬ p10) ∨ (¬ p102) ∨ (¬ p738) ∨ (¬ p756)) : (¬ p4) ∨ (¬ p10) ∨ (¬ p102) ∨ (¬ p738) ∨ (¬ p756) := by
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
  rcases h13138 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18000 (p7 p10 p108 p342 p534 p726 : Prop)
    (h16152 : (¬ p7))
    (h13139 : p7 ∨ (¬ p10) ∨ (¬ p108) ∨ (¬ p342) ∨ (¬ p534) ∨ (¬ p726)) : (¬ p10) ∨ (¬ p108) ∨ (¬ p342) ∨ (¬ p534) ∨ (¬ p726) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p342 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13139 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18001 (p7 p67 p226 p234 p344 p406 p476 p686 p883 p897 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h8348 : p1386)
    (h13140 : p7 ∨ (¬ p67) ∨ (¬ p226) ∨ (¬ p234) ∨ (¬ p344) ∨ (¬ p406) ∨ (¬ p476) ∨ p686 ∨ (¬ p883) ∨ (¬ p897) ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p67) ∨ (¬ p226) ∨ (¬ p234) ∨ (¬ p344) ∨ (¬ p406) ∨ (¬ p476) ∨ (¬ p883) ∨ (¬ p897) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
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
  have u5 : p476 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p883 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p686) := by
    exact h16205
  have u11 : p1386 := by
    exact h8348
  rcases h13140 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
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

theorem step18002 (p7 p229 p234 p406 p476 p653 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16194 : (¬ p653))
    (h8348 : p1386)
    (h13141 : p7 ∨ (¬ p229) ∨ (¬ p234) ∨ (¬ p406) ∨ (¬ p476) ∨ p653 ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p229) ∨ (¬ p234) ∨ (¬ p406) ∨ (¬ p476) ∨ (¬ p1333) := by
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
  have u2 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p476 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p653) := by
    exact h16194
  have u7 : p1386 := by
    exact h8348
  rcases h13141 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step18003 (p7 p666 p710 p904 p919 p1061 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16230 : (¬ p919))
    (h8348 : p1386)
    (h13143 : p7 ∨ (¬ p666) ∨ (¬ p710) ∨ (¬ p904) ∨ p919 ∨ (¬ p1061) ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p666) ∨ (¬ p710) ∨ (¬ p904) ∨ (¬ p1061) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p666 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p710 := by
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
  have u4 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p919) := by
    exact h16230
  have u7 : p1386 := by
    exact h8348
  rcases h13143 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step18004 (p6 p7 p8 p19 p64 p657 p875 p1100 p1187 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16220 : (¬ p875))
    (h8348 : p1386)
    (h13144 : (¬ p6) ∨ p7 ∨ (¬ p8) ∨ (¬ p19) ∨ (¬ p64) ∨ (¬ p657) ∨ p875 ∨ (¬ p1100) ∨ (¬ p1187) ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p6) ∨ (¬ p8) ∨ (¬ p19) ∨ (¬ p64) ∨ (¬ p657) ∨ (¬ p1100) ∨ (¬ p1187) ∨ (¬ p1333) := by
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
  have u4 : p657 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p875) := by
    exact h16220
  have u10 : p1386 := by
    exact h8348
  rcases h13144 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step18005 (p7 p19 p104 p229 p757 p1665 : Prop)
    (h16152 : (¬ p7))
    (h13145 : p7 ∨ (¬ p19) ∨ (¬ p104) ∨ (¬ p229) ∨ (¬ p757) ∨ (¬ p1665)) : (¬ p19) ∨ (¬ p104) ∨ (¬ p229) ∨ (¬ p757) ∨ (¬ p1665) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p757 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13145 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18006 (p6 p7 p19 p64 p86 p789 p790 p875 p1187 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16220 : (¬ p875))
    (h8348 : p1386)
    (h13146 : (¬ p6) ∨ p7 ∨ (¬ p19) ∨ (¬ p64) ∨ (¬ p86) ∨ (¬ p789) ∨ (¬ p790) ∨ p875 ∨ (¬ p1187) ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p6) ∨ (¬ p19) ∨ (¬ p64) ∨ (¬ p86) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1187) ∨ (¬ p1333) := by
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
  have u3 : p86 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p875) := by
    exact h16220
  have u10 : p1386 := by
    exact h8348
  rcases h13146 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step18008 (p7 p85 p406 p576 p656 p904 p919 p1184 p1333 p1454 p1644 : Prop)
    (h16152 : (¬ p7))
    (h16230 : (¬ p919))
    (h7053 : p1184)
    (h13148 : p7 ∨ (¬ p85) ∨ (¬ p406) ∨ (¬ p576) ∨ (¬ p656) ∨ (¬ p904) ∨ p919 ∨ (¬ p1184) ∨ (¬ p1333) ∨ (¬ p1454) ∨ (¬ p1644)) : (¬ p85) ∨ (¬ p406) ∨ (¬ p576) ∨ (¬ p656) ∨ (¬ p904) ∨ (¬ p1333) ∨ (¬ p1454) ∨ (¬ p1644) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
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
  have u6 : p1454 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1644 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p919) := by
    exact h16230
  have u10 : p1184 := by
    exact h7053
  rcases h13148 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step18010 (p7 p122 p123 p160 p532 p576 p1273 p1348 : Prop)
    (h16152 : (¬ p7))
    (h10260 : p122)
    (h16186 : (¬ p123))
    (h13150 : p7 ∨ (¬ p122) ∨ p123 ∨ (¬ p160) ∨ (¬ p532) ∨ (¬ p576) ∨ (¬ p1273) ∨ (¬ p1348)) : (¬ p160) ∨ (¬ p532) ∨ (¬ p576) ∨ (¬ p1273) ∨ (¬ p1348) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p122 := by
    exact h10260
  have u7 : (¬ p123) := by
    exact h16186
  rcases h13150 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step18012 (p7 p87 p1226 p1273 p1347 p1508 : Prop)
    (h16152 : (¬ p7))
    (h13152 : p7 ∨ (¬ p87) ∨ (¬ p1226) ∨ (¬ p1273) ∨ (¬ p1347) ∨ (¬ p1508)) : (¬ p87) ∨ (¬ p1226) ∨ (¬ p1273) ∨ (¬ p1347) ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13152 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18015 (p7 p45 p129 p233 p481 p1159 p1255 p1273 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h2345 : p233)
    (h13155 : p7 ∨ (¬ p45) ∨ p129 ∨ (¬ p233) ∨ (¬ p481) ∨ (¬ p1159) ∨ (¬ p1255) ∨ (¬ p1273)) : (¬ p45) ∨ (¬ p481) ∨ (¬ p1159) ∨ (¬ p1255) ∨ (¬ p1273) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
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
  have u3 : p1255 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p129) := by
    exact h16154
  have u7 : p233 := by
    exact h2345
  rcases h13155 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step18017 (p7 p19 p44 p124 p207 p802 p1077 p1124 p1249 p1393 : Prop)
    (h16152 : (¬ p7))
    (h13157 : p7 ∨ (¬ p19) ∨ (¬ p44) ∨ (¬ p124) ∨ (¬ p207) ∨ (¬ p802) ∨ (¬ p1077) ∨ (¬ p1124) ∨ (¬ p1249) ∨ (¬ p1393)) : (¬ p19) ∨ (¬ p44) ∨ (¬ p124) ∨ (¬ p207) ∨ (¬ p802) ∨ (¬ p1077) ∨ (¬ p1124) ∨ (¬ p1249) ∨ (¬ p1393) := by
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
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p802 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h13157 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18018 (p7 p19 p40 p124 p207 p226 p233 p344 p481 p727 p940 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h2345 : p233)
    (h13158 : p7 ∨ (¬ p19) ∨ p40 ∨ (¬ p124) ∨ (¬ p207) ∨ (¬ p226) ∨ (¬ p233) ∨ (¬ p344) ∨ (¬ p481) ∨ (¬ p727) ∨ (¬ p940)) : (¬ p19) ∨ (¬ p124) ∨ (¬ p207) ∨ (¬ p226) ∨ (¬ p344) ∨ (¬ p481) ∨ (¬ p727) ∨ (¬ p940) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p124 := by
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
  have u4 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p727 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p40) := by
    exact h16150
  have u10 : p233 := by
    exact h2345
  rcases h13158 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u9 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step18019 (p7 p19 p44 p124 p207 p533 p756 p802 p858 p1325 : Prop)
    (h16152 : (¬ p7))
    (h13159 : p7 ∨ (¬ p19) ∨ (¬ p44) ∨ (¬ p124) ∨ (¬ p207) ∨ (¬ p533) ∨ (¬ p756) ∨ (¬ p802) ∨ (¬ p858) ∨ (¬ p1325)) : (¬ p19) ∨ (¬ p44) ∨ (¬ p124) ∨ (¬ p207) ∨ (¬ p533) ∨ (¬ p756) ∨ (¬ p802) ∨ (¬ p858) ∨ (¬ p1325) := by
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
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p802 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h13159 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18020 (p7 p85 p124 p496 p533 p756 p1249 p1489 : Prop)
    (h16152 : (¬ p7))
    (h13160 : p7 ∨ (¬ p85) ∨ (¬ p124) ∨ (¬ p496) ∨ (¬ p533) ∨ (¬ p756) ∨ (¬ p1249) ∨ (¬ p1489)) : (¬ p85) ∨ (¬ p124) ∨ (¬ p496) ∨ (¬ p533) ∨ (¬ p756) ∨ (¬ p1249) ∨ (¬ p1489) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
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
  have u3 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p756 := by
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
  rcases h13160 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18021 (p7 p230 p256 p288 p814 p1075 p1393 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h6478 : p1075)
    (h13162 : p7 ∨ p230 ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p814) ∨ (¬ p1075) ∨ (¬ p1393)) : (¬ p256) ∨ (¬ p288) ∨ (¬ p814) ∨ (¬ p1393) := by
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
  have u5 : (¬ p230) := by
    exact h16165
  have u6 : p1075 := by
    exact h6478
  rcases h13162 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step18022 (p7 p342 p420 p462 p532 p1078 p1225 : Prop)
    (h16152 : (¬ p7))
    (h13165 : p7 ∨ (¬ p342) ∨ (¬ p420) ∨ (¬ p462) ∨ (¬ p532) ∨ (¬ p1078) ∨ (¬ p1225)) : (¬ p342) ∨ (¬ p420) ∨ (¬ p462) ∨ (¬ p532) ∨ (¬ p1078) ∨ (¬ p1225) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p342 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p462 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1078 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h13165 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step18023 (p7 p303 p603 p1225 p1293 p1325 : Prop)
    (h16152 : (¬ p7))
    (h13166 : p7 ∨ (¬ p303) ∨ (¬ p603) ∨ (¬ p1225) ∨ (¬ p1293) ∨ (¬ p1325)) : (¬ p303) ∨ (¬ p603) ∨ (¬ p1225) ∨ (¬ p1293) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p603 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1293 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13166 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18024 (p7 p19 p207 p347 p362 p540 p1187 : Prop)
    (h16152 : (¬ p7))
    (h13167 : p7 ∨ (¬ p19) ∨ (¬ p207) ∨ (¬ p347) ∨ (¬ p362) ∨ (¬ p540) ∨ (¬ p1187)) : (¬ p19) ∨ (¬ p207) ∨ (¬ p347) ∨ (¬ p362) ∨ (¬ p540) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p540 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h13167 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step18025 (p7 p19 p67 p102 p206 p304 : Prop)
    (h16152 : (¬ p7))
    (h13168 : p7 ∨ (¬ p19) ∨ (¬ p67) ∨ (¬ p102) ∨ (¬ p206) ∨ (¬ p304)) : (¬ p19) ∨ (¬ p67) ∨ (¬ p102) ∨ (¬ p206) ∨ (¬ p304) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13168 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18027 (p7 p344 p406 p686 p690 p728 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h6744 : p1135)
    (h13170 : p7 ∨ (¬ p344) ∨ (¬ p406) ∨ p686 ∨ (¬ p690) ∨ (¬ p728) ∨ (¬ p1135)) : (¬ p344) ∨ (¬ p406) ∨ (¬ p690) ∨ (¬ p728) := by
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
  have u2 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p686) := by
    exact h16205
  have u6 : p1135 := by
    exact h6744
  rcases h13170 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step18028 (p7 p67 p226 p234 p406 p431 p476 p734 p883 p897 : Prop)
    (h16152 : (¬ p7))
    (h13171 : p7 ∨ (¬ p67) ∨ (¬ p226) ∨ (¬ p234) ∨ (¬ p406) ∨ (¬ p431) ∨ (¬ p476) ∨ (¬ p734) ∨ (¬ p883) ∨ (¬ p897)) : (¬ p67) ∨ (¬ p226) ∨ (¬ p234) ∨ (¬ p406) ∨ (¬ p431) ∨ (¬ p476) ∨ (¬ p734) ∨ (¬ p883) ∨ (¬ p897) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
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
  have u5 : p476 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p883 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h13171 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18029 (p7 p67 p226 p234 p476 p687 p883 p980 p1074 p1330 : Prop)
    (h16152 : (¬ p7))
    (h13172 : p7 ∨ (¬ p67) ∨ (¬ p226) ∨ (¬ p234) ∨ (¬ p476) ∨ (¬ p687) ∨ (¬ p883) ∨ (¬ p980) ∨ (¬ p1074) ∨ (¬ p1330)) : (¬ p67) ∨ (¬ p226) ∨ (¬ p234) ∨ (¬ p476) ∨ (¬ p687) ∨ (¬ p883) ∨ (¬ p980) ∨ (¬ p1074) ∨ (¬ p1330) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p476 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p883 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h13172 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18030 (p7 p19 p67 p161 p207 p226 p227 p883 p983 p1081 p1306 : Prop)
    (h16152 : (¬ p7))
    (h13173 : p7 ∨ (¬ p19) ∨ (¬ p67) ∨ (¬ p161) ∨ (¬ p207) ∨ (¬ p226) ∨ (¬ p227) ∨ (¬ p883) ∨ (¬ p983) ∨ (¬ p1081) ∨ (¬ p1306)) : (¬ p19) ∨ (¬ p67) ∨ (¬ p161) ∨ (¬ p207) ∨ (¬ p226) ∨ (¬ p227) ∨ (¬ p883) ∨ (¬ p983) ∨ (¬ p1081) ∨ (¬ p1306) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p207 := by
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
  have u6 : p883 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h13173 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step18031 (p7 p11 p85 p389 p576 p686 p983 p1077 p1184 p1325 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h7053 : p1184)
    (h13174 : p7 ∨ (¬ p11) ∨ (¬ p85) ∨ (¬ p389) ∨ (¬ p576) ∨ p686 ∨ (¬ p983) ∨ (¬ p1077) ∨ (¬ p1184) ∨ (¬ p1325)) : (¬ p11) ∨ (¬ p85) ∨ (¬ p389) ∨ (¬ p576) ∨ (¬ p983) ∨ (¬ p1077) ∨ (¬ p1325) := by
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
  have u2 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p686) := by
    exact h16205
  have u9 : p1184 := by
    exact h7053
  rcases h13174 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18032 (p7 p258 p456 p495 p686 p1184 p1443 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h7053 : p1184)
    (h13175 : p7 ∨ (¬ p258) ∨ (¬ p456) ∨ (¬ p495) ∨ p686 ∨ (¬ p1184) ∨ (¬ p1443)) : (¬ p258) ∨ (¬ p456) ∨ (¬ p495) ∨ (¬ p1443) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
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
  have u3 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p686) := by
    exact h16205
  have u6 : p1184 := by
    exact h7053
  rcases h13175 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step18033 (p7 p125 p265 p288 p426 p438 p728 p1075 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h6478 : p1075)
    (h13176 : p7 ∨ (¬ p125) ∨ (¬ p265) ∨ (¬ p288) ∨ p426 ∨ (¬ p438) ∨ (¬ p728) ∨ (¬ p1075)) : (¬ p125) ∨ (¬ p265) ∨ (¬ p288) ∨ (¬ p438) ∨ (¬ p728) := by
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
  have u2 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p426) := by
    exact h16178
  have u7 : p1075 := by
    exact h6478
  rcases h13176 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step18034 (p7 p67 p226 p234 p669 p883 p1002 p1035 p1074 p1325 : Prop)
    (h16152 : (¬ p7))
    (h13177 : p7 ∨ (¬ p67) ∨ (¬ p226) ∨ (¬ p234) ∨ (¬ p669) ∨ (¬ p883) ∨ (¬ p1002) ∨ (¬ p1035) ∨ (¬ p1074) ∨ (¬ p1325)) : (¬ p67) ∨ (¬ p226) ∨ (¬ p234) ∨ (¬ p669) ∨ (¬ p883) ∨ (¬ p1002) ∨ (¬ p1035) ∨ (¬ p1074) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p226 := by
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
  have u4 : p883 := by
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
  have u7 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h13177 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18035 (p7 p67 p226 p423 p669 p883 p1035 p1074 p1325 : Prop)
    (h16152 : (¬ p7))
    (h13178 : p7 ∨ (¬ p67) ∨ (¬ p226) ∨ (¬ p423) ∨ (¬ p669) ∨ (¬ p883) ∨ (¬ p1035) ∨ (¬ p1074) ∨ (¬ p1325)) : (¬ p67) ∨ (¬ p226) ∨ (¬ p423) ∨ (¬ p669) ∨ (¬ p883) ∨ (¬ p1035) ∨ (¬ p1074) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p883 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13178 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18036 (p7 p362 p434 p496 p980 p1074 p1099 p1330 : Prop)
    (h16152 : (¬ p7))
    (h13179 : p7 ∨ (¬ p362) ∨ (¬ p434) ∨ (¬ p496) ∨ (¬ p980) ∨ (¬ p1074) ∨ (¬ p1099) ∨ (¬ p1330)) : (¬ p362) ∨ (¬ p434) ∨ (¬ p496) ∨ (¬ p980) ∨ (¬ p1074) ∨ (¬ p1099) ∨ (¬ p1330) := by
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
  have u2 : p496 := by
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
  have u5 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13179 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18037 (p7 p346 p904 p980 p1074 p1075 p1324 : Prop)
    (h16152 : (¬ p7))
    (h6478 : p1075)
    (h16309 : (¬ p1324))
    (h13180 : p7 ∨ (¬ p346) ∨ (¬ p904) ∨ (¬ p980) ∨ (¬ p1074) ∨ (¬ p1075) ∨ p1324) : (¬ p346) ∨ (¬ p904) ∨ (¬ p980) ∨ (¬ p1074) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p904 := by
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
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p1075 := by
    exact h6478
  have u6 : (¬ p1324) := by
    exact h16309
  rcases h13180 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)

theorem step18038 (p7 p20 p124 p207 p234 p330 p636 : Prop)
    (h16152 : (¬ p7))
    (h13181 : p7 ∨ (¬ p20) ∨ (¬ p124) ∨ (¬ p207) ∨ (¬ p234) ∨ (¬ p330) ∨ (¬ p636)) : (¬ p20) ∨ (¬ p124) ∨ (¬ p207) ∨ (¬ p234) ∨ (¬ p330) ∨ (¬ p636) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p20 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h13181 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step18039 (p6 p7 p142 p188 p790 p802 : Prop)
    (h16152 : (¬ p7))
    (h13182 : (¬ p6) ∨ p7 ∨ (¬ p142) ∨ (¬ p188) ∨ (¬ p790) ∨ (¬ p802)) : (¬ p6) ∨ (¬ p142) ∨ (¬ p188) ∨ (¬ p790) ∨ (¬ p802) := by
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
  rcases h13182 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18040 (p7 p16 p499 p633 p665 p814 p858 p1077 : Prop)
    (h16152 : (¬ p7))
    (h13183 : p7 ∨ (¬ p16) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p665) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1077)) : (¬ p16) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p665) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
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
  rcases h13183 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18041 (p7 p126 p258 p427 p499 p633 p1136 : Prop)
    (h16152 : (¬ p7))
    (h2334 : p427)
    (h16259 : (¬ p1136))
    (h13184 : p7 ∨ (¬ p126) ∨ (¬ p258) ∨ (¬ p427) ∨ (¬ p499) ∨ (¬ p633) ∨ p1136) : (¬ p126) ∨ (¬ p258) ∨ (¬ p499) ∨ (¬ p633) := by
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
  rcases h13184 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step18042 (p6 p7 p45 p192 p330 p801 p1393 : Prop)
    (h16152 : (¬ p7))
    (h13185 : (¬ p6) ∨ p7 ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p330) ∨ (¬ p801) ∨ (¬ p1393)) : (¬ p6) ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p330) ∨ (¬ p801) ∨ (¬ p1393) := by
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
  have u3 : p330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p801 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h13185 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step18043 (p7 p90 p256 p382 p574 p633 p665 p819 p1077 p1385 : Prop)
    (h16152 : (¬ p7))
    (h13186 : p7 ∨ (¬ p90) ∨ (¬ p256) ∨ (¬ p382) ∨ (¬ p574) ∨ (¬ p633) ∨ (¬ p665) ∨ (¬ p819) ∨ (¬ p1077) ∨ (¬ p1385)) : (¬ p90) ∨ (¬ p256) ∨ (¬ p382) ∨ (¬ p574) ∨ (¬ p633) ∨ (¬ p665) ∨ (¬ p819) ∨ (¬ p1077) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p90 := by
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
  have u3 : p574 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p819 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h13186 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18044 (p7 p18 p43 p142 p802 p1393 : Prop)
    (h16152 : (¬ p7))
    (h13188 : p7 ∨ (¬ p18) ∨ (¬ p43) ∨ (¬ p142) ∨ (¬ p802) ∨ (¬ p1393)) : (¬ p18) ∨ (¬ p43) ∨ (¬ p142) ∨ (¬ p802) ∨ (¬ p1393) := by
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
  have u2 : p142 := by
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
  rcases h13188 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18045 (p7 p63 p124 p421 p577 p616 p665 p858 p1077 p1388 : Prop)
    (h16152 : (¬ p7))
    (h13191 : p7 ∨ (¬ p63) ∨ (¬ p124) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p616) ∨ (¬ p665) ∨ (¬ p858) ∨ (¬ p1077) ∨ (¬ p1388)) : (¬ p63) ∨ (¬ p124) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p616) ∨ (¬ p665) ∨ (¬ p858) ∨ (¬ p1077) ∨ (¬ p1388) := by
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
  have u6 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1388 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h13191 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18046 (p7 p18 p63 p69 p129 p142 p792 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h4535 : p792)
    (h13193 : p7 ∨ (¬ p18) ∨ (¬ p63) ∨ (¬ p69) ∨ p129 ∨ (¬ p142) ∨ (¬ p792)) : (¬ p18) ∨ (¬ p63) ∨ (¬ p69) ∨ (¬ p142) := by
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
  have u2 : p69 := by
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
  have u6 : p792 := by
    exact h4535
  rcases h13193 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step18047 (p6 p7 p257 p303 p427 p481 p996 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h2334 : p427)
    (h13194 : (¬ p6) ∨ p7 ∨ p257 ∨ (¬ p303) ∨ (¬ p427) ∨ (¬ p481) ∨ (¬ p996)) : (¬ p6) ∨ (¬ p303) ∨ (¬ p481) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p303 := by
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
  have u5 : (¬ p257) := by
    exact h16170
  have u6 : p427 := by
    exact h2334
  rcases h13194 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step18048 (p7 p90 p256 p574 p633 p665 p858 p1077 p1385 : Prop)
    (h16152 : (¬ p7))
    (h13195 : p7 ∨ (¬ p90) ∨ (¬ p256) ∨ (¬ p574) ∨ (¬ p633) ∨ (¬ p665) ∨ (¬ p858) ∨ (¬ p1077) ∨ (¬ p1385)) : (¬ p90) ∨ (¬ p256) ∨ (¬ p574) ∨ (¬ p633) ∨ (¬ p665) ∨ (¬ p858) ∨ (¬ p1077) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p90 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p574 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p665 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13195 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18049 (p7 p344 p382 p499 p621 p633 p789 p842 : Prop)
    (h16152 : (¬ p7))
    (h13196 : p7 ∨ (¬ p344) ∨ (¬ p382) ∨ (¬ p499) ∨ (¬ p621) ∨ (¬ p633) ∨ (¬ p789) ∨ (¬ p842)) : (¬ p344) ∨ (¬ p382) ∨ (¬ p499) ∨ (¬ p621) ∨ (¬ p633) ∨ (¬ p789) ∨ (¬ p842) := by
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
  have u3 : p621 := by
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
  have u6 : p842 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13196 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18050 (p7 p18 p330 p382 p480 p1193 p1286 : Prop)
    (h16152 : (¬ p7))
    (h13197 : p7 ∨ (¬ p18) ∨ (¬ p330) ∨ (¬ p382) ∨ (¬ p480) ∨ (¬ p1193) ∨ (¬ p1286)) : (¬ p18) ∨ (¬ p330) ∨ (¬ p382) ∨ (¬ p480) ∨ (¬ p1193) ∨ (¬ p1286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p330 := by
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
  have u4 : p1193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h13197 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step18052 (p7 p86 p193 p424 p431 p616 p996 p1545 : Prop)
    (h16152 : (¬ p7))
    (h13200 : p7 ∨ (¬ p86) ∨ (¬ p193) ∨ (¬ p424) ∨ (¬ p431) ∨ (¬ p616) ∨ (¬ p996) ∨ (¬ p1545)) : (¬ p86) ∨ (¬ p193) ∨ (¬ p424) ∨ (¬ p431) ∨ (¬ p616) ∨ (¬ p996) ∨ (¬ p1545) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p86 := by
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
  have u3 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13200 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18053 (p7 p18 p129 p142 p279 p382 p815 p1193 p1286 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h1444 : p279)
    (h13201 : p7 ∨ (¬ p18) ∨ p129 ∨ (¬ p142) ∨ (¬ p279) ∨ (¬ p382) ∨ (¬ p815) ∨ (¬ p1193) ∨ (¬ p1286)) : (¬ p18) ∨ (¬ p142) ∨ (¬ p382) ∨ (¬ p815) ∨ (¬ p1193) ∨ (¬ p1286) := by
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
  have u2 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p815 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p129) := by
    exact h16154
  have u8 : p279 := by
    exact h1444
  rcases h13201 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)

theorem step18055 (p7 p86 p126 p256 p387 p431 p616 p1545 : Prop)
    (h16152 : (¬ p7))
    (h13203 : p7 ∨ (¬ p86) ∨ (¬ p126) ∨ (¬ p256) ∨ (¬ p387) ∨ (¬ p431) ∨ (¬ p616) ∨ (¬ p1545)) : (¬ p86) ∨ (¬ p126) ∨ (¬ p256) ∨ (¬ p387) ∨ (¬ p431) ∨ (¬ p616) ∨ (¬ p1545) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p126 := by
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
  have u4 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13203 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18056 (p7 p18 p63 p69 p124 p257 p344 p421 p577 p657 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h6744 : p1135)
    (h13204 : p7 ∨ (¬ p18) ∨ (¬ p63) ∨ (¬ p69) ∨ (¬ p124) ∨ p257 ∨ (¬ p344) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p657) ∨ (¬ p1135)) : (¬ p18) ∨ (¬ p63) ∨ (¬ p69) ∨ (¬ p124) ∨ (¬ p344) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p657) := by
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
  have u2 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p344 := by
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
  have u7 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p257) := by
    exact h16170
  have u10 : p1135 := by
    exact h6744
  rcases h13204 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step18057 (p6 p7 p128 p129 p142 p481 p1187 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16154 : (¬ p129))
    (h13205 : (¬ p6) ∨ p7 ∨ (¬ p128) ∨ p129 ∨ (¬ p142) ∨ (¬ p481) ∨ (¬ p1187)) : (¬ p6) ∨ (¬ p142) ∨ (¬ p481) ∨ (¬ p1187) := by
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
  have u5 : p128 := by
    exact h653
  have u6 : (¬ p129) := by
    exact h16154
  rcases h13205 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u5)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step18058 (p7 p22 p71 p481 p495 p1187 : Prop)
    (h16152 : (¬ p7))
    (h13206 : p7 ∨ (¬ p22) ∨ (¬ p71) ∨ (¬ p481) ∨ (¬ p495) ∨ (¬ p1187)) : (¬ p22) ∨ (¬ p71) ∨ (¬ p481) ∨ (¬ p495) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p22 := by
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
  have u4 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13206 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18059 (p6 p7 p23 p328 p420 p481 : Prop)
    (h16152 : (¬ p7))
    (h13207 : (¬ p6) ∨ p7 ∨ (¬ p23) ∨ (¬ p328) ∨ (¬ p420) ∨ (¬ p481)) : (¬ p6) ∨ (¬ p23) ∨ (¬ p328) ∨ (¬ p420) ∨ (¬ p481) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p23 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p328 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13207 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18060 (p6 p7 p139 p301 p328 p481 : Prop)
    (h16152 : (¬ p7))
    (h13208 : (¬ p6) ∨ p7 ∨ (¬ p139) ∨ (¬ p301) ∨ (¬ p328) ∨ (¬ p481)) : (¬ p6) ∨ (¬ p139) ∨ (¬ p301) ∨ (¬ p328) ∨ (¬ p481) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p139 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p328 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13208 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18061 (p7 p63 p128 p481 p928 p1044 p1116 p1136 p1159 p1187 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16259 : (¬ p1136))
    (h13209 : p7 ∨ (¬ p63) ∨ (¬ p128) ∨ (¬ p481) ∨ (¬ p928) ∨ (¬ p1044) ∨ (¬ p1116) ∨ p1136 ∨ (¬ p1159) ∨ (¬ p1187)) : (¬ p63) ∨ (¬ p481) ∨ (¬ p928) ∨ (¬ p1044) ∨ (¬ p1116) ∨ (¬ p1159) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1044 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : p128 := by
    exact h653
  have u9 : (¬ p1136) := by
    exact h16259
  rcases h13209 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18062 (p7 p124 p455 p498 p636 p1136 p1386 p1452 : Prop)
    (h16152 : (¬ p7))
    (h16259 : (¬ p1136))
    (h8348 : p1386)
    (h13210 : p7 ∨ (¬ p124) ∨ (¬ p455) ∨ (¬ p498) ∨ (¬ p636) ∨ p1136 ∨ (¬ p1386) ∨ (¬ p1452)) : (¬ p124) ∨ (¬ p455) ∨ (¬ p498) ∨ (¬ p636) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p1136) := by
    exact h16259
  have u7 : p1386 := by
    exact h8348
  rcases h13210 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step18063 (p7 p72 p160 p1141 p1168 p1465 : Prop)
    (h16152 : (¬ p7))
    (h13211 : p7 ∨ (¬ p72) ∨ (¬ p160) ∨ (¬ p1141) ∨ (¬ p1168) ∨ (¬ p1465)) : (¬ p72) ∨ (¬ p160) ∨ (¬ p1141) ∨ (¬ p1168) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1168 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13211 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18064 (p7 p124 p434 p498 p601 p636 p685 p1136 : Prop)
    (h16152 : (¬ p7))
    (h3898 : p685)
    (h16259 : (¬ p1136))
    (h13212 : p7 ∨ (¬ p124) ∨ (¬ p434) ∨ (¬ p498) ∨ (¬ p601) ∨ (¬ p636) ∨ (¬ p685) ∨ p1136) : (¬ p124) ∨ (¬ p434) ∨ (¬ p498) ∨ (¬ p601) ∨ (¬ p636) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p498 := by
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
  have u6 : p685 := by
    exact h3898
  have u7 : (¬ p1136) := by
    exact h16259
  rcases h13212 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u6)
  · exact False.elim (u7 q7)

theorem step18065 (p7 p16 p124 p228 p455 p498 p636 p814 p858 : Prop)
    (h16152 : (¬ p7))
    (h13213 : p7 ∨ (¬ p16) ∨ (¬ p124) ∨ (¬ p228) ∨ (¬ p455) ∨ (¬ p498) ∨ (¬ p636) ∨ (¬ p814) ∨ (¬ p858)) : (¬ p16) ∨ (¬ p124) ∨ (¬ p228) ∨ (¬ p455) ∨ (¬ p498) ∨ (¬ p636) ∨ (¬ p814) ∨ (¬ p858) := by
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
  have u2 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p636 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13213 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18066 (p6 p7 p257 p427 p456 p601 p1140 p1211 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h2334 : p427)
    (h13214 : (¬ p6) ∨ p7 ∨ p257 ∨ (¬ p427) ∨ (¬ p456) ∨ (¬ p601) ∨ (¬ p1140) ∨ (¬ p1211)) : (¬ p6) ∨ (¬ p456) ∨ (¬ p601) ∨ (¬ p1140) ∨ (¬ p1211) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p601 := by
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
  have u6 : (¬ p257) := by
    exact h16170
  have u7 : p427 := by
    exact h2334
  rcases h13214 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step18067 (p7 p128 p481 p1159 p1187 p1324 p1465 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16309 : (¬ p1324))
    (h13215 : p7 ∨ (¬ p128) ∨ (¬ p481) ∨ (¬ p1159) ∨ (¬ p1187) ∨ p1324 ∨ (¬ p1465)) : (¬ p481) ∨ (¬ p1159) ∨ (¬ p1187) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1187 := by
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
  rcases h13215 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step18068 (p7 p128 p161 p227 p481 p498 p1136 p1144 p1159 p1187 p1452 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16259 : (¬ p1136))
    (h13216 : p7 ∨ (¬ p128) ∨ (¬ p161) ∨ (¬ p227) ∨ (¬ p481) ∨ (¬ p498) ∨ p1136 ∨ (¬ p1144) ∨ (¬ p1159) ∨ (¬ p1187) ∨ (¬ p1452)) : (¬ p161) ∨ (¬ p227) ∨ (¬ p481) ∨ (¬ p498) ∨ (¬ p1144) ∨ (¬ p1159) ∨ (¬ p1187) ∨ (¬ p1452) := by
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
  have u2 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1144 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p128 := by
    exact h653
  have u10 : (¬ p1136) := by
    exact h16259
  rcases h13216 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step18071 (p2 p5 p7 p63 p228 p419 p581 p1443 : Prop)
    (h16152 : (¬ p7))
    (h13219 : (¬ p2) ∨ (¬ p5) ∨ p7 ∨ (¬ p63) ∨ (¬ p228) ∨ (¬ p419) ∨ (¬ p581) ∨ (¬ p1443)) : (¬ p2) ∨ (¬ p5) ∨ (¬ p63) ∨ (¬ p228) ∨ (¬ p419) ∨ (¬ p581) ∨ (¬ p1443) := by
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
  have u3 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13219 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18072 (p5 p7 p63 p224 p225 p226 p860 p1273 : Prop)
    (h16152 : (¬ p7))
    (h13220 : (¬ p5) ∨ p7 ∨ (¬ p63) ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p860) ∨ (¬ p1273)) : (¬ p5) ∨ (¬ p63) ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p860) ∨ (¬ p1273) := by
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
  have u5 : p860 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13220 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18073 (p7 p108 p139 p258 p309 p544 p710 : Prop)
    (h16152 : (¬ p7))
    (h13221 : p7 ∨ (¬ p108) ∨ (¬ p139) ∨ (¬ p258) ∨ (¬ p309) ∨ (¬ p544) ∨ (¬ p710)) : (¬ p108) ∨ (¬ p139) ∨ (¬ p258) ∨ (¬ p309) ∨ (¬ p544) ∨ (¬ p710) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p139 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h13221 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step18074 (p7 p124 p268 p283 p344 p836 : Prop)
    (h16152 : (¬ p7))
    (h13222 : p7 ∨ (¬ p124) ∨ (¬ p268) ∨ (¬ p283) ∨ (¬ p344) ∨ (¬ p836)) : (¬ p124) ∨ (¬ p268) ∨ (¬ p283) ∨ (¬ p344) ∨ (¬ p836) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p268 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p283 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13222 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18076 (p7 p12 p108 p139 p258 p309 p1055 : Prop)
    (h16152 : (¬ p7))
    (h13224 : p7 ∨ (¬ p12) ∨ (¬ p108) ∨ (¬ p139) ∨ (¬ p258) ∨ (¬ p309) ∨ (¬ p1055)) : (¬ p12) ∨ (¬ p108) ∨ (¬ p139) ∨ (¬ p258) ∨ (¬ p309) ∨ (¬ p1055) := by
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
  have u2 : p139 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h13224 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step18077 (p5 p7 p63 p226 p1036 p1120 p1225 p1227 p1489 : Prop)
    (h16152 : (¬ p7))
    (h13226 : (¬ p5) ∨ p7 ∨ (¬ p63) ∨ (¬ p226) ∨ (¬ p1036) ∨ (¬ p1120) ∨ (¬ p1225) ∨ (¬ p1227) ∨ (¬ p1489)) : (¬ p5) ∨ (¬ p63) ∨ (¬ p226) ∨ (¬ p1036) ∨ (¬ p1120) ∨ (¬ p1225) ∨ (¬ p1227) ∨ (¬ p1489) := by
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
  have u3 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1120 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13226 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18078 (p5 p7 p63 p226 p940 p985 p1273 p1508 : Prop)
    (h16152 : (¬ p7))
    (h13227 : (¬ p5) ∨ p7 ∨ (¬ p63) ∨ (¬ p226) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1273) ∨ (¬ p1508)) : (¬ p5) ∨ (¬ p63) ∨ (¬ p226) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1273) ∨ (¬ p1508) := by
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
  have u3 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13227 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18079 (p5 p7 p63 p226 p419 p539 p657 p838 p1393 : Prop)
    (h16152 : (¬ p7))
    (h13228 : (¬ p5) ∨ p7 ∨ (¬ p63) ∨ (¬ p226) ∨ (¬ p419) ∨ (¬ p539) ∨ (¬ p657) ∨ (¬ p838) ∨ (¬ p1393)) : (¬ p5) ∨ (¬ p63) ∨ (¬ p226) ∨ (¬ p419) ∨ (¬ p539) ∨ (¬ p657) ∨ (¬ p838) ∨ (¬ p1393) := by
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
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p539 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p657 := by
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
  rcases h13228 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18080 (p7 p11 p126 p227 p266 p331 p690 p821 p1366 : Prop)
    (h16152 : (¬ p7))
    (h13229 : p7 ∨ (¬ p11) ∨ (¬ p126) ∨ (¬ p227) ∨ (¬ p266) ∨ (¬ p331) ∨ (¬ p690) ∨ (¬ p821) ∨ (¬ p1366)) : (¬ p11) ∨ (¬ p126) ∨ (¬ p227) ∨ (¬ p266) ∨ (¬ p331) ∨ (¬ p690) ∨ (¬ p821) ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p331 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p821 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13229 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18081 (p7 p10 p102 p303 p1075 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h6478 : p1075)
    (h16309 : (¬ p1324))
    (h13231 : p7 ∨ (¬ p10) ∨ (¬ p102) ∨ (¬ p303) ∨ (¬ p1075) ∨ p1324 ∨ (¬ p1325)) : (¬ p10) ∨ (¬ p102) ∨ (¬ p303) ∨ (¬ p1325) := by
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
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p1075 := by
    exact h6478
  have u6 : (¬ p1324) := by
    exact h16309
  rcases h13231 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step18082 (p5 p7 p63 p225 p226 p668 p928 p1116 : Prop)
    (h16152 : (¬ p7))
    (h13232 : (¬ p5) ∨ p7 ∨ (¬ p63) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p668) ∨ (¬ p928) ∨ (¬ p1116)) : (¬ p5) ∨ (¬ p63) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p668) ∨ (¬ p928) ∨ (¬ p1116) := by
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
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13232 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18083 (p7 p63 p657 p840 p928 p1135 p1136 : Prop)
    (h16152 : (¬ p7))
    (h6744 : p1135)
    (h16259 : (¬ p1136))
    (h13233 : p7 ∨ (¬ p63) ∨ (¬ p657) ∨ (¬ p840) ∨ (¬ p928) ∨ (¬ p1135) ∨ p1136) : (¬ p63) ∨ (¬ p657) ∨ (¬ p840) ∨ (¬ p928) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p657 := by
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
  have u5 : p1135 := by
    exact h6744
  have u6 : (¬ p1136) := by
    exact h16259
  rcases h13233 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)

theorem step18084 (p7 p63 p224 p343 p789 p1136 p1393 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16259 : (¬ p1136))
    (h13235 : p7 ∨ (¬ p63) ∨ (¬ p224) ∨ (¬ p343) ∨ (¬ p789) ∨ p1136 ∨ (¬ p1393)) : (¬ p63) ∨ (¬ p224) ∨ (¬ p789) ∨ (¬ p1393) := by
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
  have u3 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p343 := by
    exact h1950
  have u6 : (¬ p1136) := by
    exact h16259
  rcases h13235 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step18085 (p7 p268 p301 p303 p368 p406 : Prop)
    (h16152 : (¬ p7))
    (h13236 : p7 ∨ (¬ p268) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p368) ∨ (¬ p406)) : (¬ p268) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p368) ∨ (¬ p406) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p268 := by
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
  rcases h13236 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18086 (p7 p268 p362 p387 p514 p858 : Prop)
    (h16152 : (¬ p7))
    (h13237 : p7 ∨ (¬ p268) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p514) ∨ (¬ p858)) : (¬ p268) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p514) ∨ (¬ p858) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p268 := by
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
  have u3 : p514 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13237 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18087 (p5 p7 p63 p533 p537 p928 p1159 p1465 : Prop)
    (h16152 : (¬ p7))
    (h13238 : (¬ p5) ∨ p7 ∨ (¬ p63) ∨ (¬ p533) ∨ (¬ p537) ∨ (¬ p928) ∨ (¬ p1159) ∨ (¬ p1465)) : (¬ p5) ∨ (¬ p63) ∨ (¬ p533) ∨ (¬ p537) ∨ (¬ p928) ∨ (¬ p1159) ∨ (¬ p1465) := by
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
  have u2 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p928 := by
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
  rcases h13238 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18089 (p5 p7 p89 p226 p790 p1036 p1120 p1273 p1385 : Prop)
    (h16152 : (¬ p7))
    (h13240 : (¬ p5) ∨ p7 ∨ (¬ p89) ∨ (¬ p226) ∨ (¬ p790) ∨ (¬ p1036) ∨ (¬ p1120) ∨ (¬ p1273) ∨ (¬ p1385)) : (¬ p5) ∨ (¬ p89) ∨ (¬ p226) ∨ (¬ p790) ∨ (¬ p1036) ∨ (¬ p1120) ∨ (¬ p1273) ∨ (¬ p1385) := by
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
  have u3 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1120 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13240 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18090 (p5 p7 p63 p226 p669 p789 p1036 p1393 : Prop)
    (h16152 : (¬ p7))
    (h13241 : (¬ p5) ∨ p7 ∨ (¬ p63) ∨ (¬ p226) ∨ (¬ p669) ∨ (¬ p789) ∨ (¬ p1036) ∨ (¬ p1393)) : (¬ p5) ∨ (¬ p63) ∨ (¬ p226) ∨ (¬ p669) ∨ (¬ p789) ∨ (¬ p1036) ∨ (¬ p1393) := by
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
  have u3 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13241 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18091 (p642 p1075 p1096 p1136 : Prop)
    (h6478 : p1075)
    (h16259 : (¬ p1136))
    (h13242 : p642 ∨ (¬ p1075) ∨ (¬ p1096) ∨ p1136) : p642 ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p642) := fun hu => hn (Or.inl hu)
  have u1 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p1075 := by
    exact h6478
  have u3 : (¬ p1136) := by
    exact h16259
  rcases h13242 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (u3 q3)

theorem step18092 (p3 p6 p7 p107 p139 p258 : Prop)
    (h16152 : (¬ p7))
    (h13243 : (¬ p3) ∨ (¬ p6) ∨ p7 ∨ (¬ p107) ∨ (¬ p139) ∨ (¬ p258)) : (¬ p3) ∨ (¬ p6) ∨ (¬ p107) ∨ (¬ p139) ∨ (¬ p258) := by
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
  rcases h13243 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18093 (p7 p110 p303 p345 p544 p657 : Prop)
    (h16152 : (¬ p7))
    (h13244 : p7 ∨ (¬ p110) ∨ (¬ p303) ∨ (¬ p345) ∨ (¬ p544) ∨ (¬ p657)) : (¬ p110) ∨ (¬ p303) ∨ (¬ p345) ∨ (¬ p544) ∨ (¬ p657) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p110 := by
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
  rcases h13244 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18094 (p7 p90 p256 p288 p575 p636 : Prop)
    (h16152 : (¬ p7))
    (h13245 : p7 ∨ (¬ p90) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p575) ∨ (¬ p636)) : (¬ p90) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p575) ∨ (¬ p636) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p90 := by
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
  have u3 : p575 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13245 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18095 (p7 p129 p189 p256 p288 p1077 p1139 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h6761 : p1139)
    (h13246 : p7 ∨ p129 ∨ (¬ p189) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p1077) ∨ (¬ p1139)) : (¬ p189) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p1077) := by
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
  have u2 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p129) := by
    exact h16154
  have u6 : p1139 := by
    exact h6761
  rcases h13246 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step18096 (p7 p256 p288 p302 p814 p858 p1075 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h6478 : p1075)
    (h13247 : p7 ∨ (¬ p256) ∨ (¬ p288) ∨ p302 ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1075)) : (¬ p256) ∨ (¬ p288) ∨ (¬ p814) ∨ (¬ p858) := by
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
  have u6 : p1075 := by
    exact h6478
  rcases h13247 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step18097 (p7 p12 p14 p15 p1075 p1076 p1136 : Prop)
    (h16152 : (¬ p7))
    (h6478 : p1075)
    (h16259 : (¬ p1136))
    (h13250 : p7 ∨ (¬ p12) ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p1075) ∨ (¬ p1076) ∨ p1136) : (¬ p12) ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p1076) := by
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
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p1075 := by
    exact h6478
  have u6 : (¬ p1136) := by
    exact h16259
  rcases h13250 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step18098 (p3 p7 p41 p166 p195 p918 : Prop)
    (h16152 : (¬ p7))
    (h13252 : (¬ p3) ∨ p7 ∨ (¬ p41) ∨ (¬ p166) ∨ (¬ p195) ∨ (¬ p918)) : (¬ p3) ∨ (¬ p41) ∨ (¬ p166) ∨ (¬ p195) ∨ (¬ p918) := by
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
  have u2 : p166 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13252 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18099 (p7 p12 p86 p163 p193 p616 p665 p1287 : Prop)
    (h16152 : (¬ p7))
    (h13253 : p7 ∨ (¬ p12) ∨ (¬ p86) ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p616) ∨ (¬ p665) ∨ (¬ p1287)) : (¬ p12) ∨ (¬ p86) ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p616) ∨ (¬ p665) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p86 := by
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
  have u4 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13253 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18100 (p7 p86 p163 p193 p343 p544 p616 p1287 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16309 : (¬ p1324))
    (h13254 : p7 ∨ (¬ p86) ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p343) ∨ (¬ p544) ∨ (¬ p616) ∨ (¬ p1287) ∨ p1324 ∨ (¬ p1325)) : (¬ p86) ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p544) ∨ (¬ p616) ∨ (¬ p1287) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p86 := by
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
  have u3 : p544 := by
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
  rcases h13254 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18101 (p7 p194 p256 p288 p344 p382 p477 p545 p996 : Prop)
    (h16152 : (¬ p7))
    (h13255 : p7 ∨ (¬ p194) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p382) ∨ (¬ p477) ∨ (¬ p545) ∨ (¬ p996)) : (¬ p194) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p382) ∨ (¬ p477) ∨ (¬ p545) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p194 := by
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
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p477 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13255 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18102 (p7 p126 p224 p256 p343 p387 p791 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16213 : (¬ p791))
    (h13256 : p7 ∨ (¬ p126) ∨ (¬ p224) ∨ (¬ p256) ∨ (¬ p343) ∨ (¬ p387) ∨ p791) : (¬ p126) ∨ (¬ p224) ∨ (¬ p256) ∨ (¬ p387) := by
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
  have u2 : p256 := by
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
  have u6 : (¬ p791) := by
    exact h16213
  rcases h13256 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step18103 (p7 p90 p256 p574 p633 p668 p836 p918 p1077 : Prop)
    (h16152 : (¬ p7))
    (h13258 : p7 ∨ (¬ p90) ∨ (¬ p256) ∨ (¬ p574) ∨ (¬ p633) ∨ (¬ p668) ∨ (¬ p836) ∨ (¬ p918) ∨ (¬ p1077)) : (¬ p90) ∨ (¬ p256) ∨ (¬ p574) ∨ (¬ p633) ∨ (¬ p668) ∨ (¬ p836) ∨ (¬ p918) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p90 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p574 := by
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
  have u5 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13258 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18104 (p7 p256 p576 p791 p928 p1116 p1139 : Prop)
    (h16152 : (¬ p7))
    (h16213 : (¬ p791))
    (h6761 : p1139)
    (h13259 : p7 ∨ (¬ p256) ∨ (¬ p576) ∨ p791 ∨ (¬ p928) ∨ (¬ p1116) ∨ (¬ p1139)) : (¬ p256) ∨ (¬ p576) ∨ (¬ p928) ∨ (¬ p1116) := by
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
  have u2 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p791) := by
    exact h16213
  have u6 : p1139 := by
    exact h6761
  rcases h13259 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step18105 (p7 p85 p230 p499 p633 p1077 p1139 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h6761 : p1139)
    (h13260 : p7 ∨ (¬ p85) ∨ p230 ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p1077) ∨ (¬ p1139)) : (¬ p85) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
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
  have u3 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p230) := by
    exact h16165
  have u6 : p1139 := by
    exact h6761
  rcases h13260 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step18106 (p7 p8 p167 p195 p225 p561 : Prop)
    (h16152 : (¬ p7))
    (h13261 : p7 ∨ (¬ p8) ∨ (¬ p167) ∨ (¬ p195) ∨ (¬ p225) ∨ (¬ p561)) : (¬ p8) ∨ (¬ p167) ∨ (¬ p195) ∨ (¬ p225) ∨ (¬ p561) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13261 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18107 (p2 p7 p27 p127 p325 p601 : Prop)
    (h16152 : (¬ p7))
    (h13262 : (¬ p2) ∨ p7 ∨ (¬ p27) ∨ (¬ p127) ∨ (¬ p325) ∨ (¬ p601)) : (¬ p2) ∨ (¬ p27) ∨ (¬ p127) ∨ (¬ p325) ∨ (¬ p601) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p27 := by
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
  have u4 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13262 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18108 (p7 p18 p1146 p1213 p1225 p1465 : Prop)
    (h16152 : (¬ p7))
    (h13263 : p7 ∨ (¬ p18) ∨ (¬ p1146) ∨ (¬ p1213) ∨ (¬ p1225) ∨ (¬ p1465)) : (¬ p18) ∨ (¬ p1146) ∨ (¬ p1213) ∨ (¬ p1225) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1146 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1213 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13263 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18110 (p7 p63 p125 p494 p577 p601 : Prop)
    (h16152 : (¬ p7))
    (h13266 : p7 ∨ (¬ p63) ∨ (¬ p125) ∨ (¬ p494) ∨ (¬ p577) ∨ (¬ p601)) : (¬ p63) ∨ (¬ p125) ∨ (¬ p494) ∨ (¬ p577) ∨ (¬ p601) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p125 := by
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
  have u4 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13266 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18111 (p7 p46 p163 p534 p879 p1538 : Prop)
    (h16152 : (¬ p7))
    (h13267 : p7 ∨ (¬ p46) ∨ (¬ p163) ∨ (¬ p534) ∨ (¬ p879) ∨ (¬ p1538)) : (¬ p46) ∨ (¬ p163) ∨ (¬ p534) ∨ (¬ p879) ∨ (¬ p1538) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p46 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p879 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1538 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13267 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18112 (p3 p7 p43 p71 p229 p495 p577 : Prop)
    (h16152 : (¬ p7))
    (h13268 : (¬ p3) ∨ p7 ∨ (¬ p43) ∨ (¬ p71) ∨ (¬ p229) ∨ (¬ p495) ∨ (¬ p577)) : (¬ p3) ∨ (¬ p43) ∨ (¬ p71) ∨ (¬ p229) ∨ (¬ p495) ∨ (¬ p577) := by
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
  have u2 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p229 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h13268 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step18114 (p7 p225 p426 p534 p792 p918 p1584 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h4535 : p792)
    (h13270 : p7 ∨ (¬ p225) ∨ p426 ∨ (¬ p534) ∨ (¬ p792) ∨ (¬ p918) ∨ (¬ p1584)) : (¬ p225) ∨ (¬ p534) ∨ (¬ p918) ∨ (¬ p1584) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p534 := by
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
  rcases h13270 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step18115 (p2 p7 p88 p134 p188 p257 p343 p424 p495 p577 p904 p1096 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h1950 : p343)
    (h13271 : (¬ p2) ∨ p7 ∨ (¬ p88) ∨ (¬ p134) ∨ (¬ p188) ∨ p257 ∨ (¬ p343) ∨ (¬ p424) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p904) ∨ (¬ p1096)) : (¬ p2) ∨ (¬ p88) ∨ (¬ p134) ∨ (¬ p188) ∨ (¬ p424) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p904) ∨ (¬ p1096) := by
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
  have u5 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p577 := by
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
  have u10 : (¬ p257) := by
    exact h16170
  have u11 : p343 := by
    exact h1950
  rcases h13271 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (q0 u0)
  · exact False.elim (u9 q1)
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

theorem step18116 (p7 p88 p189 p495 p545 p577 p796 p904 p1096 : Prop)
    (h16152 : (¬ p7))
    (h13272 : p7 ∨ (¬ p88) ∨ (¬ p189) ∨ (¬ p495) ∨ (¬ p545) ∨ (¬ p577) ∨ (¬ p796) ∨ (¬ p904) ∨ (¬ p1096)) : (¬ p88) ∨ (¬ p189) ∨ (¬ p495) ∨ (¬ p545) ∨ (¬ p577) ∨ (¬ p796) ∨ (¬ p904) ∨ (¬ p1096) := by
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
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p545 := by
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
  rcases h13272 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18117 (p7 p8 p9 p495 p577 p897 p922 : Prop)
    (h16152 : (¬ p7))
    (h13273 : p7 ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p897) ∨ (¬ p922)) : (¬ p8) ∨ (¬ p9) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p897) ∨ (¬ p922) := by
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
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p922 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h13273 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step18121 (p7 p159 p160 p161 p495 p577 p1236 : Prop)
    (h16152 : (¬ p7))
    (h13277 : p7 ∨ (¬ p159) ∨ (¬ p160) ∨ (¬ p161) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p1236)) : (¬ p159) ∨ (¬ p160) ∨ (¬ p161) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p1236) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p159 := by
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
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1236 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h13277 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step18122 (p7 p38 p43 p226 p461 p495 p577 p983 p1037 p1081 p1229 p1465 : Prop)
    (h16152 : (¬ p7))
    (h13278 : p7 ∨ (¬ p38) ∨ (¬ p43) ∨ (¬ p226) ∨ (¬ p461) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p983) ∨ (¬ p1037) ∨ (¬ p1081) ∨ (¬ p1229) ∨ (¬ p1465)) : (¬ p38) ∨ (¬ p43) ∨ (¬ p226) ∨ (¬ p461) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p983) ∨ (¬ p1037) ∨ (¬ p1081) ∨ (¬ p1229) ∨ (¬ p1465) := by
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
  have u2 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p461 := by
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
  have u6 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1037 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : (¬ p7) := by
    exact h16152
  rcases h13278 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
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

theorem step18123 (p7 p46 p161 p235 p1035 p1256 : Prop)
    (h16152 : (¬ p7))
    (h13279 : p7 ∨ (¬ p46) ∨ (¬ p161) ∨ (¬ p235) ∨ (¬ p1035) ∨ (¬ p1256)) : (¬ p46) ∨ (¬ p161) ∨ (¬ p235) ∨ (¬ p1035) ∨ (¬ p1256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p46 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p235 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13279 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18124 (p7 p38 p43 p134 p257 p495 p577 p1225 p1229 p1386 p1713 p1798 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h8348 : p1386)
    (h13281 : p7 ∨ (¬ p38) ∨ (¬ p43) ∨ (¬ p134) ∨ p257 ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1386) ∨ (¬ p1713) ∨ (¬ p1798)) : (¬ p38) ∨ (¬ p43) ∨ (¬ p134) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1713) ∨ (¬ p1798) := by
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
  have u2 : p134 := by
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
  have u5 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1713 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1798 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p257) := by
    exact h16170
  have u11 : p1386 := by
    exact h8348
  rcases h13281 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
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

theorem step18125 (p7 p88 p189 p495 p577 p1225 p1229 p1473 p1711 : Prop)
    (h16152 : (¬ p7))
    (h13282 : p7 ∨ (¬ p88) ∨ (¬ p189) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1473) ∨ (¬ p1711)) : (¬ p88) ∨ (¬ p189) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1473) ∨ (¬ p1711) := by
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
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p577 := by
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
  have u6 : p1473 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1711 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13282 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18126 (p7 p163 p191 p544 p556 p710 : Prop)
    (h16152 : (¬ p7))
    (h13283 : p7 ∨ (¬ p163) ∨ (¬ p191) ∨ (¬ p544) ∨ (¬ p556) ∨ (¬ p710)) : (¬ p163) ∨ (¬ p191) ∨ (¬ p544) ∨ (¬ p556) ∨ (¬ p710) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p191 := by
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
  rcases h13283 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18128 (p7 p63 p161 p792 p983 p1181 p1232 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16272 : (¬ p1181))
    (h13285 : p7 ∨ (¬ p63) ∨ (¬ p161) ∨ (¬ p792) ∨ (¬ p983) ∨ p1181 ∨ (¬ p1232)) : (¬ p63) ∨ (¬ p161) ∨ (¬ p983) ∨ (¬ p1232) := by
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
  have u5 : p792 := by
    exact h4535
  have u6 : (¬ p1181) := by
    exact h16272
  rcases h13285 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step18129 (p7 p38 p43 p163 p226 p422 p532 p1214 p1225 p1270 : Prop)
    (h16152 : (¬ p7))
    (h13286 : p7 ∨ (¬ p38) ∨ (¬ p43) ∨ (¬ p163) ∨ (¬ p226) ∨ (¬ p422) ∨ (¬ p532) ∨ (¬ p1214) ∨ (¬ p1225) ∨ (¬ p1270)) : (¬ p38) ∨ (¬ p43) ∨ (¬ p163) ∨ (¬ p226) ∨ (¬ p422) ∨ (¬ p532) ∨ (¬ p1214) ∨ (¬ p1225) ∨ (¬ p1270) := by
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
  have u2 : p163 := by
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
  have u5 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1214 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1270 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h13286 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18130 (p7 p88 p167 p189 p532 p1036 p1081 p1225 p1270 : Prop)
    (h16152 : (¬ p7))
    (h13287 : p7 ∨ (¬ p88) ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p532) ∨ (¬ p1036) ∨ (¬ p1081) ∨ (¬ p1225) ∨ (¬ p1270)) : (¬ p88) ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p532) ∨ (¬ p1036) ∨ (¬ p1081) ∨ (¬ p1225) ∨ (¬ p1270) := by
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
  have u3 : p532 := by
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
  have u6 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1270 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13287 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18131 (p7 p88 p189 p227 p421 p435 p577 p796 p1335 p1452 : Prop)
    (h16152 : (¬ p7))
    (h13288 : p7 ∨ (¬ p88) ∨ (¬ p189) ∨ (¬ p227) ∨ (¬ p421) ∨ (¬ p435) ∨ (¬ p577) ∨ (¬ p796) ∨ (¬ p1335) ∨ (¬ p1452)) : (¬ p88) ∨ (¬ p189) ∨ (¬ p227) ∨ (¬ p421) ∨ (¬ p435) ∨ (¬ p577) ∨ (¬ p796) ∨ (¬ p1335) ∨ (¬ p1452) := by
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
  have u2 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p796 := by
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
  rcases h13288 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18134 (p7 p88 p495 p577 p595 p657 p814 p858 p901 : Prop)
    (h16152 : (¬ p7))
    (h13292 : p7 ∨ (¬ p88) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p595) ∨ (¬ p657) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p901)) : (¬ p88) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p595) ∨ (¬ p657) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p901) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p901 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13292 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18135 (p7 p88 p163 p188 p226 p495 p577 p595 p796 p1191 : Prop)
    (h16152 : (¬ p7))
    (h13293 : p7 ∨ (¬ p88) ∨ (¬ p163) ∨ (¬ p188) ∨ (¬ p226) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p595) ∨ (¬ p796) ∨ (¬ p1191)) : (¬ p88) ∨ (¬ p163) ∨ (¬ p188) ∨ (¬ p226) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p595) ∨ (¬ p796) ∨ (¬ p1191) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p88 := by
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
  have u7 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h13293 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18136 (p2 p7 p188 p224 p279 p302 p435 p728 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16285 : (¬ p302))
    (h13294 : (¬ p2) ∨ p7 ∨ (¬ p188) ∨ (¬ p224) ∨ (¬ p279) ∨ p302 ∨ (¬ p435) ∨ (¬ p728)) : (¬ p2) ∨ (¬ p188) ∨ (¬ p224) ∨ (¬ p435) ∨ (¬ p728) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
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
  have u3 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p279 := by
    exact h1444
  have u7 : (¬ p302) := by
    exact h16285
  rcases h13294 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)
  · exact False.elim (u7 q5)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step18137 (p7 p134 p257 p424 p1366 p1545 p1664 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h10244 : p1664)
    (h13295 : p7 ∨ (¬ p134) ∨ p257 ∨ (¬ p424) ∨ (¬ p1366) ∨ (¬ p1545) ∨ (¬ p1664)) : (¬ p134) ∨ (¬ p424) ∨ (¬ p1366) ∨ (¬ p1545) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p134 := by
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
  have u5 : (¬ p257) := by
    exact h16170
  have u6 : p1664 := by
    exact h10244
  rcases h13295 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step18138 (p7 p185 p227 p263 p734 p836 p1335 p1452 : Prop)
    (h16152 : (¬ p7))
    (h13296 : p7 ∨ (¬ p185) ∨ (¬ p227) ∨ (¬ p263) ∨ (¬ p734) ∨ (¬ p836) ∨ (¬ p1335) ∨ (¬ p1452)) : (¬ p185) ∨ (¬ p227) ∨ (¬ p263) ∨ (¬ p734) ∨ (¬ p836) ∨ (¬ p1335) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p263 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p836 := by
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
  rcases h13296 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18139 (p7 p88 p163 p188 p226 p387 p438 p577 p600 p796 p875 p1135 p1542 : Prop)
    (h16152 : (¬ p7))
    (h16220 : (¬ p875))
    (h6744 : p1135)
    (h13297 : p7 ∨ (¬ p88) ∨ (¬ p163) ∨ (¬ p188) ∨ (¬ p226) ∨ (¬ p387) ∨ (¬ p438) ∨ (¬ p577) ∨ (¬ p600) ∨ (¬ p796) ∨ p875 ∨ (¬ p1135) ∨ (¬ p1542)) : (¬ p88) ∨ (¬ p163) ∨ (¬ p188) ∨ (¬ p226) ∨ (¬ p387) ∨ (¬ p438) ∨ (¬ p577) ∨ (¬ p600) ∨ (¬ p796) ∨ (¬ p1542) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p88 := by
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
  have u4 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p600 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  have u11 : (¬ p875) := by
    exact h16220
  have u12 : p1135 := by
    exact h6744
  rcases h13297 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
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
  · exact False.elim (u11 q10)
  · exact False.elim (q11 u12)
  · exact False.elim (q12 u9)

theorem step18141 (p7 p88 p163 p188 p226 p362 p387 p421 p422 p577 p1004 : Prop)
    (h16152 : (¬ p7))
    (h13299 : p7 ∨ (¬ p88) ∨ (¬ p163) ∨ (¬ p188) ∨ (¬ p226) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p421) ∨ (¬ p422) ∨ (¬ p577) ∨ (¬ p1004)) : (¬ p88) ∨ (¬ p163) ∨ (¬ p188) ∨ (¬ p226) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p421) ∨ (¬ p422) ∨ (¬ p577) ∨ (¬ p1004) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p88 := by
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
  have u4 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h13299 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step18142 (p7 p163 p226 p302 p419 p659 p796 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h3753 : p659)
    (h13300 : p7 ∨ (¬ p163) ∨ (¬ p226) ∨ p302 ∨ (¬ p419) ∨ (¬ p659) ∨ (¬ p796)) : (¬ p163) ∨ (¬ p226) ∨ (¬ p419) ∨ (¬ p796) := by
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
  have u5 : (¬ p302) := by
    exact h16285
  have u6 : p659 := by
    exact h3753
  rcases h13300 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step18143 (p7 p163 p188 p226 p303 p331 p406 p796 p817 : Prop)
    (h16152 : (¬ p7))
    (h13301 : p7 ∨ (¬ p163) ∨ (¬ p188) ∨ (¬ p226) ∨ (¬ p303) ∨ (¬ p331) ∨ (¬ p406) ∨ (¬ p796) ∨ (¬ p817)) : (¬ p163) ∨ (¬ p188) ∨ (¬ p226) ∨ (¬ p303) ∨ (¬ p331) ∨ (¬ p406) ∨ (¬ p796) ∨ (¬ p817) := by
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
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p331 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p817 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13301 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18144 (p7 p88 p167 p189 p495 p577 p1036 p1229 p1309 : Prop)
    (h16152 : (¬ p7))
    (h13302 : p7 ∨ (¬ p88) ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p1036) ∨ (¬ p1229) ∨ (¬ p1309)) : (¬ p88) ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p1036) ∨ (¬ p1229) ∨ (¬ p1309) := by
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
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13302 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18145 (p7 p167 p189 p227 p263 p940 p985 p1452 : Prop)
    (h16152 : (¬ p7))
    (h13303 : p7 ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p227) ∨ (¬ p263) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1452)) : (¬ p167) ∨ (¬ p189) ∨ (¬ p227) ∨ (¬ p263) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1452) := by
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
  have u2 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p263 := by
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
  have u6 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13303 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18147 (p7 p226 p426 p537 p659 p836 p940 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h3753 : p659)
    (h13307 : p7 ∨ (¬ p226) ∨ p426 ∨ (¬ p537) ∨ (¬ p659) ∨ (¬ p836) ∨ (¬ p940)) : (¬ p226) ∨ (¬ p537) ∨ (¬ p836) ∨ (¬ p940) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p426) := by
    exact h16178
  have u6 : p659 := by
    exact h3753
  rcases h13307 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step18149 (p7 p362 p387 p421 p537 p577 p669 p922 p1115 p1538 : Prop)
    (h16152 : (¬ p7))
    (h13309 : p7 ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p421) ∨ (¬ p537) ∨ (¬ p577) ∨ (¬ p669) ∨ (¬ p922) ∨ (¬ p1115) ∨ (¬ p1538)) : (¬ p362) ∨ (¬ p387) ∨ (¬ p421) ∨ (¬ p537) ∨ (¬ p577) ∨ (¬ p669) ∨ (¬ p922) ∨ (¬ p1115) ∨ (¬ p1538) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p922 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1538 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h13309 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18150 (p7 p303 p347 p368 p406 p421 p537 p577 p836 p922 p1538 : Prop)
    (h16152 : (¬ p7))
    (h13310 : p7 ∨ (¬ p303) ∨ (¬ p347) ∨ (¬ p368) ∨ (¬ p406) ∨ (¬ p421) ∨ (¬ p537) ∨ (¬ p577) ∨ (¬ p836) ∨ (¬ p922) ∨ (¬ p1538)) : (¬ p303) ∨ (¬ p347) ∨ (¬ p368) ∨ (¬ p406) ∨ (¬ p421) ∨ (¬ p537) ∨ (¬ p577) ∨ (¬ p836) ∨ (¬ p922) ∨ (¬ p1538) := by
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
  have u2 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p922 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1538 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h13310 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step18151 (p7 p534 p792 p918 p1036 p1181 p1584 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16272 : (¬ p1181))
    (h13312 : p7 ∨ (¬ p534) ∨ (¬ p792) ∨ (¬ p918) ∨ (¬ p1036) ∨ p1181 ∨ (¬ p1584)) : (¬ p534) ∨ (¬ p918) ∨ (¬ p1036) ∨ (¬ p1584) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p534 := by
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
  have u3 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p792 := by
    exact h4535
  have u6 : (¬ p1181) := by
    exact h16272
  rcases h13312 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step18154 (p7 p15 p46 p1142 p1232 p1256 : Prop)
    (h16152 : (¬ p7))
    (h13315 : p7 ∨ (¬ p15) ∨ (¬ p46) ∨ (¬ p1142) ∨ (¬ p1232) ∨ (¬ p1256)) : (¬ p15) ∨ (¬ p46) ∨ (¬ p1142) ∨ (¬ p1232) ∨ (¬ p1256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p46 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13315 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18155 (p2 p7 p88 p124 p188 p421 p422 p424 p577 p1044 p1077 : Prop)
    (h16152 : (¬ p7))
    (h13316 : (¬ p2) ∨ p7 ∨ (¬ p88) ∨ (¬ p124) ∨ (¬ p188) ∨ (¬ p421) ∨ (¬ p422) ∨ (¬ p424) ∨ (¬ p577) ∨ (¬ p1044) ∨ (¬ p1077)) : (¬ p2) ∨ (¬ p88) ∨ (¬ p124) ∨ (¬ p188) ∨ (¬ p421) ∨ (¬ p422) ∨ (¬ p424) ∨ (¬ p577) ∨ (¬ p1044) ∨ (¬ p1077) := by
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
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1044 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h13316 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step18156 (p7 p15 p46 p424 p616 p1189 : Prop)
    (h16152 : (¬ p7))
    (h13317 : p7 ∨ (¬ p15) ∨ (¬ p46) ∨ (¬ p424) ∨ (¬ p616) ∨ (¬ p1189)) : (¬ p15) ∨ (¬ p46) ∨ (¬ p424) ∨ (¬ p616) ∨ (¬ p1189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p46 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13317 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18157 (p7 p63 p710 p904 p924 p1097 : Prop)
    (h16152 : (¬ p7))
    (h13319 : p7 ∨ (¬ p63) ∨ (¬ p710) ∨ (¬ p904) ∨ (¬ p924) ∨ (¬ p1097)) : (¬ p63) ∨ (¬ p710) ∨ (¬ p904) ∨ (¬ p924) ∨ (¬ p1097) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1097 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13319 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18158 (p7 p63 p310 p421 p577 p983 p1061 p1232 p1295 p1325 : Prop)
    (h16152 : (¬ p7))
    (h13320 : p7 ∨ (¬ p63) ∨ (¬ p310) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1232) ∨ (¬ p1295) ∨ (¬ p1325)) : (¬ p63) ∨ (¬ p310) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1232) ∨ (¬ p1295) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p310 := by
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
  have u4 : p983 := by
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
  have u7 : p1295 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h13320 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18159 (p4 p7 p8 p189 p263 p310 p387 p1333 p1473 p1711 : Prop)
    (h16152 : (¬ p7))
    (h13322 : (¬ p4) ∨ p7 ∨ (¬ p8) ∨ (¬ p189) ∨ (¬ p263) ∨ (¬ p310) ∨ (¬ p387) ∨ (¬ p1333) ∨ (¬ p1473) ∨ (¬ p1711)) : (¬ p4) ∨ (¬ p8) ∨ (¬ p189) ∨ (¬ p263) ∨ (¬ p310) ∨ (¬ p387) ∨ (¬ p1333) ∨ (¬ p1473) ∨ (¬ p1711) := by
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
  have u2 : p189 := by
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
  have u5 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1473 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1711 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h13322 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18160 (p4 p7 p8 p43 p134 p257 p310 p387 p421 p577 p1333 p1386 p1710 p1713 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h8348 : p1386)
    (h13323 : (¬ p4) ∨ p7 ∨ (¬ p8) ∨ (¬ p43) ∨ (¬ p134) ∨ p257 ∨ (¬ p310) ∨ (¬ p387) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p1333) ∨ (¬ p1386) ∨ (¬ p1710) ∨ (¬ p1713)) : (¬ p4) ∨ (¬ p8) ∨ (¬ p43) ∨ (¬ p134) ∨ (¬ p310) ∨ (¬ p387) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p1333) ∨ (¬ p1710) ∨ (¬ p1713) := by
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
  have u2 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p387 := by
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
  have u8 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p1713 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : (¬ p7) := by
    exact h16152
  have u12 : (¬ p257) := by
    exact h16170
  have u13 : p1386 := by
    exact h8348
  rcases h13323 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13
  · exact False.elim (q0 u0)
  · exact False.elim (u11 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u12 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u8)
  · exact False.elim (q11 u13)
  · exact False.elim (q12 u9)
  · exact False.elim (q13 u10)

theorem step18161 (p7 p15 p88 p134 p189 p495 p577 p1693 p1712 : Prop)
    (h16152 : (¬ p7))
    (h13324 : p7 ∨ (¬ p15) ∨ (¬ p88) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p1693) ∨ (¬ p1712)) : (¬ p15) ∨ (¬ p88) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p1693) ∨ (¬ p1712) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
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
  have u4 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1693 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1712 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13324 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18162 (p7 p63 p161 p362 p421 p434 p577 p1232 p1330 : Prop)
    (h16152 : (¬ p7))
    (h13325 : p7 ∨ (¬ p63) ∨ (¬ p161) ∨ (¬ p362) ∨ (¬ p421) ∨ (¬ p434) ∨ (¬ p577) ∨ (¬ p1232) ∨ (¬ p1330)) : (¬ p63) ∨ (¬ p161) ∨ (¬ p362) ∨ (¬ p421) ∨ (¬ p434) ∨ (¬ p577) ∨ (¬ p1232) ∨ (¬ p1330) := by
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
  have u2 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13325 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18163 (p7 p63 p1225 p1226 p1230 p1270 : Prop)
    (h16152 : (¬ p7))
    (h13327 : p7 ∨ (¬ p63) ∨ (¬ p1225) ∨ (¬ p1226) ∨ (¬ p1230) ∨ (¬ p1270)) : (¬ p63) ∨ (¬ p1225) ∨ (¬ p1226) ∨ (¬ p1230) ∨ (¬ p1270) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1230 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1270 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13327 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18164 (p7 p46 p142 p207 p310 p879 p1061 p1074 : Prop)
    (h16152 : (¬ p7))
    (h13329 : p7 ∨ (¬ p46) ∨ (¬ p142) ∨ (¬ p207) ∨ (¬ p310) ∨ (¬ p879) ∨ (¬ p1061) ∨ (¬ p1074)) : (¬ p46) ∨ (¬ p142) ∨ (¬ p207) ∨ (¬ p310) ∨ (¬ p879) ∨ (¬ p1061) ∨ (¬ p1074) := by
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
  have u3 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p879 := by
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
  rcases h13329 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18165 (p7 p134 p257 p328 p420 p424 p633 p1075 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h6478 : p1075)
    (h13330 : p7 ∨ (¬ p134) ∨ p257 ∨ (¬ p328) ∨ (¬ p420) ∨ (¬ p424) ∨ (¬ p633) ∨ (¬ p1075)) : (¬ p134) ∨ (¬ p328) ∨ (¬ p420) ∨ (¬ p424) ∨ (¬ p633) := by
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
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p257) := by
    exact h16170
  have u7 : p1075 := by
    exact h6478
  rcases h13330 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step18166 (p7 p16 p434 p499 p601 p1330 p1349 p1489 : Prop)
    (h16152 : (¬ p7))
    (h13331 : p7 ∨ (¬ p16) ∨ (¬ p434) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1330) ∨ (¬ p1349) ∨ (¬ p1489)) : (¬ p16) ∨ (¬ p434) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1330) ∨ (¬ p1349) ∨ (¬ p1489) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
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
  have u4 : p1330 := by
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
  rcases h13331 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18167 (p7 p544 p710 p882 p1061 p1074 : Prop)
    (h16152 : (¬ p7))
    (h13332 : p7 ∨ (¬ p544) ∨ (¬ p710) ∨ (¬ p882) ∨ (¬ p1061) ∨ (¬ p1074)) : (¬ p544) ∨ (¬ p710) ∨ (¬ p882) ∨ (¬ p1061) ∨ (¬ p1074) := by
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
  have u2 : p882 := by
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
  rcases h13332 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18169 (p5 p7 p134 p257 p387 p499 p601 p1135 p1159 p1256 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h6744 : p1135)
    (h13334 : (¬ p5) ∨ p7 ∨ (¬ p134) ∨ p257 ∨ (¬ p387) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1135) ∨ (¬ p1159) ∨ (¬ p1256)) : (¬ p5) ∨ (¬ p134) ∨ (¬ p387) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1159) ∨ (¬ p1256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p134 := by
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
  rcases h13334 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (u8 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)

theorem step18170 (p7 p16 p189 p387 p422 p499 p601 p1004 : Prop)
    (h16152 : (¬ p7))
    (h13335 : p7 ∨ (¬ p16) ∨ (¬ p189) ∨ (¬ p387) ∨ (¬ p422) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1004)) : (¬ p16) ∨ (¬ p189) ∨ (¬ p387) ∨ (¬ p422) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1004) := by
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
  have u2 : p387 := by
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
  have u5 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13335 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18171 (p7 p16 p189 p228 p419 p455 p499 p796 : Prop)
    (h16152 : (¬ p7))
    (h13336 : p7 ∨ (¬ p16) ∨ (¬ p189) ∨ (¬ p228) ∨ (¬ p419) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p796)) : (¬ p16) ∨ (¬ p189) ∨ (¬ p228) ∨ (¬ p419) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p796) := by
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
  have u2 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
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
  have u6 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13336 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18172 (p5 p7 p134 p163 p226 p257 p387 p499 p601 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h6744 : p1135)
    (h13337 : (¬ p5) ∨ p7 ∨ (¬ p134) ∨ (¬ p163) ∨ (¬ p226) ∨ p257 ∨ (¬ p387) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1135)) : (¬ p5) ∨ (¬ p134) ∨ (¬ p163) ∨ (¬ p226) ∨ (¬ p387) ∨ (¬ p499) ∨ (¬ p601) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
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
  have u3 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p387 := by
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
  have u8 : (¬ p257) := by
    exact h16170
  have u9 : p1135 := by
    exact h6744
  rcases h13337 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u8 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u9)

theorem step18173 (p7 p63 p362 p387 p421 p426 p577 p897 p1099 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h8348 : p1386)
    (h13338 : p7 ∨ (¬ p63) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p421) ∨ p426 ∨ (¬ p577) ∨ (¬ p897) ∨ (¬ p1099) ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p63) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p897) ∨ (¬ p1099) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
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
  have u3 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p577 := by
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
  rcases h13338 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step18174 (p7 p63 p347 p368 p421 p438 p577 p687 p897 p1099 : Prop)
    (h16152 : (¬ p7))
    (h13339 : p7 ∨ (¬ p63) ∨ (¬ p347) ∨ (¬ p368) ∨ (¬ p421) ∨ (¬ p438) ∨ (¬ p577) ∨ (¬ p687) ∨ (¬ p897) ∨ (¬ p1099)) : (¬ p63) ∨ (¬ p347) ∨ (¬ p368) ∨ (¬ p421) ∨ (¬ p438) ∨ (¬ p577) ∨ (¬ p687) ∨ (¬ p897) ∨ (¬ p1099) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p687 := by
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
  rcases h13339 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18175 (p7 p331 p438 p796 p1371 p1713 : Prop)
    (h16152 : (¬ p7))
    (h13341 : p7 ∨ (¬ p331) ∨ (¬ p438) ∨ (¬ p796) ∨ (¬ p1371) ∨ (¬ p1713)) : (¬ p331) ∨ (¬ p438) ∨ (¬ p796) ∨ (¬ p1371) ∨ (¬ p1713) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p331 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1371 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1713 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13341 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18176 (p7 p88 p124 p189 p421 p577 p983 p1077 p1473 p1711 : Prop)
    (h16152 : (¬ p7))
    (h13342 : p7 ∨ (¬ p88) ∨ (¬ p124) ∨ (¬ p189) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p983) ∨ (¬ p1077) ∨ (¬ p1473) ∨ (¬ p1711)) : (¬ p88) ∨ (¬ p124) ∨ (¬ p189) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p983) ∨ (¬ p1077) ∨ (¬ p1473) ∨ (¬ p1711) := by
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
  have u2 : p189 := by
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
  have u5 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1473 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1711 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h13342 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18177 (p7 p124 p189 p263 p344 p422 p657 p1004 : Prop)
    (h16152 : (¬ p7))
    (h13343 : p7 ∨ (¬ p124) ∨ (¬ p189) ∨ (¬ p263) ∨ (¬ p344) ∨ (¬ p422) ∨ (¬ p657) ∨ (¬ p1004)) : (¬ p124) ∨ (¬ p189) ∨ (¬ p263) ∨ (¬ p344) ∨ (¬ p422) ∨ (¬ p657) ∨ (¬ p1004) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p263 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
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
  have u6 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13343 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18178 (p7 p124 p189 p263 p422 p533 p756 p1465 : Prop)
    (h16152 : (¬ p7))
    (h13344 : p7 ∨ (¬ p124) ∨ (¬ p189) ∨ (¬ p263) ∨ (¬ p422) ∨ (¬ p533) ∨ (¬ p756) ∨ (¬ p1465)) : (¬ p124) ∨ (¬ p189) ∨ (¬ p263) ∨ (¬ p422) ∨ (¬ p533) ∨ (¬ p756) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p263 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13344 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18179 (p7 p63 p227 p421 p577 p980 p1044 p1142 p1232 p1452 : Prop)
    (h16152 : (¬ p7))
    (h13346 : p7 ∨ (¬ p63) ∨ (¬ p227) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p980) ∨ (¬ p1044) ∨ (¬ p1142) ∨ (¬ p1232) ∨ (¬ p1452)) : (¬ p63) ∨ (¬ p227) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p980) ∨ (¬ p1044) ∨ (¬ p1142) ∨ (¬ p1232) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p227 := by
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
  have u4 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1044 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h13346 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18180 (p7 p160 p189 p228 p419 p532 p796 p1350 : Prop)
    (h16152 : (¬ p7))
    (h13347 : p7 ∨ (¬ p160) ∨ (¬ p189) ∨ (¬ p228) ∨ (¬ p419) ∨ (¬ p532) ∨ (¬ p796) ∨ (¬ p1350)) : (¬ p160) ∨ (¬ p189) ∨ (¬ p228) ∨ (¬ p419) ∨ (¬ p532) ∨ (¬ p796) ∨ (¬ p1350) := by
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
  have u2 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13347 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18181 (p7 p63 p792 p980 p1074 p1099 p1324 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16309 : (¬ p1324))
    (h13348 : p7 ∨ (¬ p63) ∨ (¬ p792) ∨ (¬ p980) ∨ (¬ p1074) ∨ (¬ p1099) ∨ p1324) : (¬ p63) ∨ (¬ p980) ∨ (¬ p1074) ∨ (¬ p1099) := by
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
  have u5 : p792 := by
    exact h4535
  have u6 : (¬ p1324) := by
    exact h16309
  rcases h13348 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step18182 (p7 p15 p46 p163 p880 p1099 : Prop)
    (h16152 : (¬ p7))
    (h13349 : p7 ∨ (¬ p15) ∨ (¬ p46) ∨ (¬ p163) ∨ (¬ p880) ∨ (¬ p1099)) : (¬ p15) ∨ (¬ p46) ∨ (¬ p163) ∨ (¬ p880) ∨ (¬ p1099) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p46 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p880 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13349 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18184 (p7 p8 p189 p239 p346 p422 p1044 p1077 : Prop)
    (h16152 : (¬ p7))
    (h13352 : p7 ∨ (¬ p8) ∨ (¬ p189) ∨ (¬ p239) ∨ (¬ p346) ∨ (¬ p422) ∨ (¬ p1044) ∨ (¬ p1077)) : (¬ p8) ∨ (¬ p189) ∨ (¬ p239) ∨ (¬ p346) ∨ (¬ p422) ∨ (¬ p1044) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p239 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1044 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13352 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18185 (p7 p63 p124 p421 p577 p668 p897 p1077 p1099 : Prop)
    (h16152 : (¬ p7))
    (h13353 : p7 ∨ (¬ p63) ∨ (¬ p124) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p668) ∨ (¬ p897) ∨ (¬ p1077) ∨ (¬ p1099)) : (¬ p63) ∨ (¬ p124) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p668) ∨ (¬ p897) ∨ (¬ p1077) ∨ (¬ p1099) := by
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
  have u4 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13353 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18186 (p7 p63 p123 p126 p420 p495 p792 : Prop)
    (h16152 : (¬ p7))
    (h16186 : (¬ p123))
    (h4535 : p792)
    (h13354 : p7 ∨ (¬ p63) ∨ p123 ∨ (¬ p126) ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p792)) : (¬ p63) ∨ (¬ p126) ∨ (¬ p420) ∨ (¬ p495) := by
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
  have u5 : (¬ p123) := by
    exact h16186
  have u6 : p792 := by
    exact h4535
  rcases h13354 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step18187 (p7 p15 p128 p257 p301 p323 p495 p574 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16170 : (¬ p257))
    (h13355 : p7 ∨ (¬ p15) ∨ (¬ p128) ∨ p257 ∨ (¬ p301) ∨ (¬ p323) ∨ (¬ p495) ∨ (¬ p574)) : (¬ p15) ∨ (¬ p301) ∨ (¬ p323) ∨ (¬ p495) ∨ (¬ p574) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p323 := by
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
  have u6 : p128 := by
    exact h653
  have u7 : (¬ p257) := by
    exact h16170
  rcases h13355 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (u7 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step18188 (p7 p63 p224 p362 p387 p421 p577 p616 p906 : Prop)
    (h16152 : (¬ p7))
    (h13357 : p7 ∨ (¬ p63) ∨ (¬ p224) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p616) ∨ (¬ p906)) : (¬ p63) ∨ (¬ p224) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p616) ∨ (¬ p906) := by
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
  have u2 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p387 := by
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
  rcases h13357 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18189 (p7 p63 p362 p387 p421 p577 p669 p1074 p1099 : Prop)
    (h16152 : (¬ p7))
    (h13358 : p7 ∨ (¬ p63) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p669) ∨ (¬ p1074) ∨ (¬ p1099)) : (¬ p63) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p669) ∨ (¬ p1074) ∨ (¬ p1099) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
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
  have u3 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p669 := by
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
  rcases h13358 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18191 (p7 p134 p188 p257 p303 p406 p434 p685 p817 p1713 p1798 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h3898 : p685)
    (h13360 : p7 ∨ (¬ p134) ∨ (¬ p188) ∨ p257 ∨ (¬ p303) ∨ (¬ p406) ∨ (¬ p434) ∨ (¬ p685) ∨ (¬ p817) ∨ (¬ p1713) ∨ (¬ p1798)) : (¬ p134) ∨ (¬ p188) ∨ (¬ p303) ∨ (¬ p406) ∨ (¬ p434) ∨ (¬ p817) ∨ (¬ p1713) ∨ (¬ p1798) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p188 := by
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
  have u4 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p817 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1713 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1798 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p257) := by
    exact h16170
  have u10 : p685 := by
    exact h3898
  rcases h13360 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step18192 (p7 p43 p71 p495 p577 p1710 p1805 : Prop)
    (h16152 : (¬ p7))
    (h13361 : p7 ∨ (¬ p43) ∨ (¬ p71) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p1710) ∨ (¬ p1805)) : (¬ p43) ∨ (¬ p71) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p1710) ∨ (¬ p1805) := by
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
  have u4 : p1710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1805 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h13361 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step18193 (p7 p15 p49 p84 p406 p820 p838 p858 p897 p1099 : Prop)
    (h16152 : (¬ p7))
    (h13362 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p406) ∨ (¬ p820) ∨ (¬ p838) ∨ (¬ p858) ∨ (¬ p897) ∨ (¬ p1099)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p406) ∨ (¬ p820) ∨ (¬ p838) ∨ (¬ p858) ∨ (¬ p897) ∨ (¬ p1099) := by
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
  have u3 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p820 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p838 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p858 := by
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
  rcases h13362 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18194 (p7 p15 p49 p84 p126 p256 p387 p1232 p1295 : Prop)
    (h16152 : (¬ p7))
    (h13363 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p126) ∨ (¬ p256) ∨ (¬ p387) ∨ (¬ p1232) ∨ (¬ p1295)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p126) ∨ (¬ p256) ∨ (¬ p387) ∨ (¬ p1232) ∨ (¬ p1295) := by
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
  rcases h13363 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18196 (p7 p15 p49 p84 p124 p266 p344 p657 p1232 p1295 : Prop)
    (h16152 : (¬ p7))
    (h13365 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p124) ∨ (¬ p266) ∨ (¬ p344) ∨ (¬ p657) ∨ (¬ p1232) ∨ (¬ p1295)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p124) ∨ (¬ p266) ∨ (¬ p344) ∨ (¬ p657) ∨ (¬ p1232) ∨ (¬ p1295) := by
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
  have u3 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1295 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h13365 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18197 (p7 p15 p49 p84 p256 p288 p344 p616 p906 : Prop)
    (h16152 : (¬ p7))
    (h13366 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p616) ∨ (¬ p906)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p616) ∨ (¬ p906) := by
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
  have u4 : p288 := by
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
  have u7 : p906 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13366 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18198 (p7 p15 p49 p84 p124 p161 p266 p533 p756 p1232 : Prop)
    (h16152 : (¬ p7))
    (h13367 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p124) ∨ (¬ p161) ∨ (¬ p266) ∨ (¬ p533) ∨ (¬ p756) ∨ (¬ p1232)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p124) ∨ (¬ p161) ∨ (¬ p266) ∨ (¬ p533) ∨ (¬ p756) ∨ (¬ p1232) := by
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
  have u3 : p124 := by
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
  have u6 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h13367 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18199 (p7 p15 p49 p84 p237 p980 p1122 p1232 p1313 p1508 : Prop)
    (h16152 : (¬ p7))
    (h13368 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p237) ∨ (¬ p980) ∨ (¬ p1122) ∨ (¬ p1232) ∨ (¬ p1313) ∨ (¬ p1508)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p237) ∨ (¬ p980) ∨ (¬ p1122) ∨ (¬ p1232) ∨ (¬ p1313) ∨ (¬ p1508) := by
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
  have u4 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1122 := by
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
  have u8 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h13368 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18200 (p7 p15 p49 p84 p224 p266 p362 p387 p616 p906 : Prop)
    (h16152 : (¬ p7))
    (h13369 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p224) ∨ (¬ p266) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p616) ∨ (¬ p906)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p224) ∨ (¬ p266) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p616) ∨ (¬ p906) := by
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
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p906 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h13369 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18201 (p2 p7 p38 p49 p84 p124 p255 p266 p435 p983 p1116 p1335 : Prop)
    (h16152 : (¬ p7))
    (h13370 : (¬ p2) ∨ p7 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p124) ∨ (¬ p255) ∨ (¬ p266) ∨ (¬ p435) ∨ (¬ p983) ∨ (¬ p1116) ∨ (¬ p1335)) : (¬ p2) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p124) ∨ (¬ p255) ∨ (¬ p266) ∨ (¬ p435) ∨ (¬ p983) ∨ (¬ p1116) ∨ (¬ p1335) := by
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
  have u2 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p255 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : (¬ p7) := by
    exact h16152
  rcases h13370 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (q0 u0)
  · exact False.elim (u11 q1)
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

theorem step18202 (p7 p15 p49 p84 p669 p789 p790 p1074 p1099 : Prop)
    (h16152 : (¬ p7))
    (h13371 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p669) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1074) ∨ (¬ p1099)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p669) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1074) ∨ (¬ p1099) := by
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
  rcases h13371 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18203 (p7 p15 p49 p84 p161 p266 p288 p1075 p1232 p1324 p1631 p1644 : Prop)
    (h16152 : (¬ p7))
    (h6478 : p1075)
    (h16309 : (¬ p1324))
    (h13372 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p161) ∨ (¬ p266) ∨ (¬ p288) ∨ (¬ p1075) ∨ (¬ p1232) ∨ p1324 ∨ (¬ p1631) ∨ (¬ p1644)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p161) ∨ (¬ p266) ∨ (¬ p288) ∨ (¬ p1232) ∨ (¬ p1631) ∨ (¬ p1644) := by
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
  have u3 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1631 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1644 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : p1075 := by
    exact h6478
  have u11 : (¬ p1324) := by
    exact h16309
  rcases h13372 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
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

theorem step18204 (p7 p15 p49 p84 p161 p256 p1232 p1449 p1651 : Prop)
    (h16152 : (¬ p7))
    (h13373 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p161) ∨ (¬ p256) ∨ (¬ p1232) ∨ (¬ p1449) ∨ (¬ p1651)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p161) ∨ (¬ p256) ∨ (¬ p1232) ∨ (¬ p1449) ∨ (¬ p1651) := by
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
  have u3 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1449 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1651 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13373 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18205 (p7 p11 p227 p266 p288 p756 p791 p1603 : Prop)
    (h16152 : (¬ p7))
    (h16213 : (¬ p791))
    (h9837 : p1603)
    (h13374 : p7 ∨ (¬ p11) ∨ (¬ p227) ∨ (¬ p266) ∨ (¬ p288) ∨ (¬ p756) ∨ p791 ∨ (¬ p1603)) : (¬ p11) ∨ (¬ p227) ∨ (¬ p266) ∨ (¬ p288) ∨ (¬ p756) := by
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
  have u2 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p791) := by
    exact h16213
  have u7 : p1603 := by
    exact h9837
  rcases h13374 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u6 q6)
  · exact False.elim (q7 u7)

theorem step18206 (p7 p121 p257 p288 p1075 p1452 p1489 p1492 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h6478 : p1075)
    (h13375 : p7 ∨ (¬ p121) ∨ p257 ∨ (¬ p288) ∨ (¬ p1075) ∨ (¬ p1452) ∨ (¬ p1489) ∨ (¬ p1492)) : (¬ p121) ∨ (¬ p288) ∨ (¬ p1452) ∨ (¬ p1489) ∨ (¬ p1492) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1492 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p257) := by
    exact h16170
  have u7 : p1075 := by
    exact h6478
  rcases h13375 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step18207 (p7 p15 p49 p84 p1232 p1295 p1325 p1346 p1508 : Prop)
    (h16152 : (¬ p7))
    (h13376 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p1232) ∨ (¬ p1295) ∨ (¬ p1325) ∨ (¬ p1346) ∨ (¬ p1508)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p1232) ∨ (¬ p1295) ∨ (¬ p1325) ∨ (¬ p1346) ∨ (¬ p1508) := by
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
  rcases h13376 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18208 (p7 p11 p84 p227 p266 p288 p534 p929 p1036 p1075 p1181 p1538 : Prop)
    (h16152 : (¬ p7))
    (h6478 : p1075)
    (h16272 : (¬ p1181))
    (h13377 : p7 ∨ (¬ p11) ∨ (¬ p84) ∨ (¬ p227) ∨ (¬ p266) ∨ (¬ p288) ∨ (¬ p534) ∨ (¬ p929) ∨ (¬ p1036) ∨ (¬ p1075) ∨ p1181 ∨ (¬ p1538)) : (¬ p11) ∨ (¬ p84) ∨ (¬ p227) ∨ (¬ p266) ∨ (¬ p288) ∨ (¬ p534) ∨ (¬ p929) ∨ (¬ p1036) ∨ (¬ p1538) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p227 := by
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
  have u5 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1538 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : p1075 := by
    exact h6478
  have u11 : (¬ p1181) := by
    exact h16272
  rcases h13377 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
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

theorem step18209 (p7 p84 p225 p256 p426 p534 p929 p1386 p1443 p1452 p1538 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h8348 : p1386)
    (h13378 : p7 ∨ (¬ p84) ∨ (¬ p225) ∨ (¬ p256) ∨ p426 ∨ (¬ p534) ∨ (¬ p929) ∨ (¬ p1386) ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p1538)) : (¬ p84) ∨ (¬ p225) ∨ (¬ p256) ∨ (¬ p534) ∨ (¬ p929) ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p1538) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p929 := by
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
  rcases h13378 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step18210 (p7 p11 p126 p194 p225 p226 p227 p266 p347 : Prop)
    (h16152 : (¬ p7))
    (h13379 : p7 ∨ (¬ p11) ∨ (¬ p126) ∨ (¬ p194) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p227) ∨ (¬ p266) ∨ (¬ p347)) : (¬ p11) ∨ (¬ p126) ∨ (¬ p194) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p227) ∨ (¬ p266) ∨ (¬ p347) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
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
  have u4 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13379 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18211 (p7 p15 p21 p423 p495 p1213 : Prop)
    (h16152 : (¬ p7))
    (h13380 : p7 ∨ (¬ p15) ∨ (¬ p21) ∨ (¬ p423) ∨ (¬ p495) ∨ (¬ p1213)) : (¬ p15) ∨ (¬ p21) ∨ (¬ p423) ∨ (¬ p495) ∨ (¬ p1213) := by
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
  have u2 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1213 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13380 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18212 (p7 p49 p71 p85 p1140 p1141 : Prop)
    (h16152 : (¬ p7))
    (h13381 : p7 ∨ (¬ p49) ∨ (¬ p71) ∨ (¬ p85) ∨ (¬ p1140) ∨ (¬ p1141)) : (¬ p49) ∨ (¬ p71) ∨ (¬ p85) ∨ (¬ p1140) ∨ (¬ p1141) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
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
  rcases h13381 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18213 (p7 p126 p194 p256 p434 p1159 p1330 p1465 : Prop)
    (h16152 : (¬ p7))
    (h13382 : p7 ∨ (¬ p126) ∨ (¬ p194) ∨ (¬ p256) ∨ (¬ p434) ∨ (¬ p1159) ∨ (¬ p1330) ∨ (¬ p1465)) : (¬ p126) ∨ (¬ p194) ∨ (¬ p256) ∨ (¬ p434) ∨ (¬ p1159) ∨ (¬ p1330) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p126 := by
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
  have u3 : p434 := by
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
  rcases h13382 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18214 (p7 p194 p256 p288 p1035 p1044 p1077 p1163 p1226 : Prop)
    (h16152 : (¬ p7))
    (h13383 : p7 ∨ (¬ p194) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p1035) ∨ (¬ p1044) ∨ (¬ p1077) ∨ (¬ p1163) ∨ (¬ p1226)) : (¬ p194) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p1035) ∨ (¬ p1044) ∨ (¬ p1077) ∨ (¬ p1163) ∨ (¬ p1226) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p194 := by
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
  have u6 : p1163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13383 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18215 (p7 p256 p343 p576 p791 p840 p928 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16213 : (¬ p791))
    (h13385 : p7 ∨ (¬ p256) ∨ (¬ p343) ∨ (¬ p576) ∨ p791 ∨ (¬ p840) ∨ (¬ p928)) : (¬ p256) ∨ (¬ p576) ∨ (¬ p840) ∨ (¬ p928) := by
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
  rcases h13385 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step18217 (p5 p7 p89 p256 p533 p574 p633 p756 p1159 p1465 : Prop)
    (h16152 : (¬ p7))
    (h13387 : (¬ p5) ∨ p7 ∨ (¬ p89) ∨ (¬ p256) ∨ (¬ p533) ∨ (¬ p574) ∨ (¬ p633) ∨ (¬ p756) ∨ (¬ p1159) ∨ (¬ p1465)) : (¬ p5) ∨ (¬ p89) ∨ (¬ p256) ∨ (¬ p533) ∨ (¬ p574) ∨ (¬ p633) ∨ (¬ p756) ∨ (¬ p1159) ∨ (¬ p1465) := by
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
  have u2 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p574 := by
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
  have u7 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h13387 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18218 (p7 p303 p348 p727 p789 p839 p1584 : Prop)
    (h16152 : (¬ p7))
    (h13388 : p7 ∨ (¬ p303) ∨ (¬ p348) ∨ (¬ p727) ∨ (¬ p789) ∨ (¬ p839) ∨ (¬ p1584)) : (¬ p303) ∨ (¬ p348) ∨ (¬ p727) ∨ (¬ p789) ∨ (¬ p839) ∨ (¬ p1584) := by
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
  have u2 : p727 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p839 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h13388 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step18219 (p7 p86 p256 p288 p344 p664 p1074 p1099 : Prop)
    (h16152 : (¬ p7))
    (h13389 : p7 ∨ (¬ p86) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p664) ∨ (¬ p1074) ∨ (¬ p1099)) : (¬ p86) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p664) ∨ (¬ p1074) ∨ (¬ p1099) := by
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
  have u3 : p344 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13389 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18220 (p7 p27 p103 p225 p344 p633 : Prop)
    (h16152 : (¬ p7))
    (h13390 : p7 ∨ (¬ p27) ∨ (¬ p103) ∨ (¬ p225) ∨ (¬ p344) ∨ (¬ p633)) : (¬ p27) ∨ (¬ p103) ∨ (¬ p225) ∨ (¬ p344) ∨ (¬ p633) := by
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
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13390 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18221 (p7 p90 p256 p344 p574 p633 p727 p918 p1584 : Prop)
    (h16152 : (¬ p7))
    (h13392 : p7 ∨ (¬ p90) ∨ (¬ p256) ∨ (¬ p344) ∨ (¬ p574) ∨ (¬ p633) ∨ (¬ p727) ∨ (¬ p918) ∨ (¬ p1584)) : (¬ p90) ∨ (¬ p256) ∨ (¬ p344) ∨ (¬ p574) ∨ (¬ p633) ∨ (¬ p727) ∨ (¬ p918) ∨ (¬ p1584) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p90 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
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
  rcases h13392 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18222 (p7 p27 p324 p434 p435 p601 : Prop)
    (h16152 : (¬ p7))
    (h13393 : p7 ∨ (¬ p27) ∨ (¬ p324) ∨ (¬ p434) ∨ (¬ p435) ∨ (¬ p601)) : (¬ p27) ∨ (¬ p324) ∨ (¬ p434) ∨ (¬ p435) ∨ (¬ p601) := by
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
  have u2 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13393 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18223 (p7 p10 p143 p438 p519 p1022 : Prop)
    (h16152 : (¬ p7))
    (h13394 : p7 ∨ (¬ p10) ∨ (¬ p143) ∨ (¬ p438) ∨ (¬ p519) ∨ (¬ p1022)) : (¬ p10) ∨ (¬ p143) ∨ (¬ p438) ∨ (¬ p519) ∨ (¬ p1022) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13394 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18224 (p3 p7 p10 p25 p133 p229 p601 p788 : Prop)
    (h16152 : (¬ p7))
    (h16157 : (¬ p133))
    (h5066 : p788)
    (h13395 : (¬ p3) ∨ p7 ∨ (¬ p10) ∨ (¬ p25) ∨ p133 ∨ (¬ p229) ∨ (¬ p601) ∨ (¬ p788)) : (¬ p3) ∨ (¬ p10) ∨ (¬ p25) ∨ (¬ p229) ∨ (¬ p601) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p25 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p133) := by
    exact h16157
  have u7 : p788 := by
    exact h5066
  rcases h13395 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step18225 (p7 p256 p286 p343 p344 p576 p791 p928 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16213 : (¬ p791))
    (h13397 : p7 ∨ (¬ p256) ∨ (¬ p286) ∨ (¬ p343) ∨ (¬ p344) ∨ (¬ p576) ∨ p791 ∨ (¬ p928)) : (¬ p256) ∨ (¬ p286) ∨ (¬ p344) ∨ (¬ p576) ∨ (¬ p928) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p286 := by
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
  have u4 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p343 := by
    exact h1950
  have u7 : (¬ p791) := by
    exact h16213
  rcases h13397 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u7 q6)
  · exact False.elim (q7 u4)

theorem step18226 (p7 p90 p241 p256 p344 p574 p633 p664 p918 p1055 : Prop)
    (h16152 : (¬ p7))
    (h13398 : p7 ∨ (¬ p90) ∨ (¬ p241) ∨ (¬ p256) ∨ (¬ p344) ∨ (¬ p574) ∨ (¬ p633) ∨ (¬ p664) ∨ (¬ p918) ∨ (¬ p1055)) : (¬ p90) ∨ (¬ p241) ∨ (¬ p256) ∨ (¬ p344) ∨ (¬ p574) ∨ (¬ p633) ∨ (¬ p664) ∨ (¬ p918) ∨ (¬ p1055) := by
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
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p574 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p664 := by
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
  rcases h13398 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18227 (p38 p63 p67 p792 p1136 : Prop)
    (h4535 : p792)
    (h16259 : (¬ p1136))
    (h13400 : (¬ p38) ∨ (¬ p63) ∨ p67 ∨ (¬ p792) ∨ p1136) : (¬ p38) ∨ (¬ p63) ∨ p67 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p67) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p792 := by
    exact h4535
  have u4 : (¬ p1136) := by
    exact h16259
  rcases h13400 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)

theorem step18229 (p7 p12 p168 p237 p1118 p1349 : Prop)
    (h16152 : (¬ p7))
    (h13402 : p7 ∨ (¬ p12) ∨ (¬ p168) ∨ (¬ p237) ∨ (¬ p1118) ∨ (¬ p1349)) : (¬ p12) ∨ (¬ p168) ∨ (¬ p237) ∨ (¬ p1118) ∨ (¬ p1349) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p168 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p237 := by
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
  rcases h13402 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18230 (p7 p11 p12 p110 p288 p1079 : Prop)
    (h16152 : (¬ p7))
    (h13403 : p7 ∨ (¬ p11) ∨ (¬ p12) ∨ (¬ p110) ∨ (¬ p288) ∨ (¬ p1079)) : (¬ p11) ∨ (¬ p12) ∨ (¬ p110) ∨ (¬ p288) ∨ (¬ p1079) := by
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
  have u2 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1079 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13403 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18232 (p7 p12 p108 p330 p481 p556 p1055 : Prop)
    (h16152 : (¬ p7))
    (h13405 : p7 ∨ (¬ p12) ∨ (¬ p108) ∨ (¬ p330) ∨ (¬ p481) ∨ (¬ p556) ∨ (¬ p1055)) : (¬ p12) ∨ (¬ p108) ∨ (¬ p330) ∨ (¬ p481) ∨ (¬ p556) ∨ (¬ p1055) := by
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
  have u2 : p330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p481 := by
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
  rcases h13405 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step18234 (p7 p85 p88 p302 p343 p344 p419 p639 p690 p821 p1096 p1366 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h1950 : p343)
    (h13407 : p7 ∨ (¬ p85) ∨ (¬ p88) ∨ p302 ∨ (¬ p343) ∨ (¬ p344) ∨ (¬ p419) ∨ (¬ p639) ∨ (¬ p690) ∨ (¬ p821) ∨ (¬ p1096) ∨ (¬ p1366)) : (¬ p85) ∨ (¬ p88) ∨ (¬ p344) ∨ (¬ p419) ∨ (¬ p639) ∨ (¬ p690) ∨ (¬ p821) ∨ (¬ p1096) ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p88 := by
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
  have u4 : p639 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p821 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p302) := by
    exact h16285
  have u11 : p343 := by
    exact h1950
  rcases h13407 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u10 q3)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step18235 (p2 p5 p7 p89 p228 p256 p419 p576 p1273 p1495 : Prop)
    (h16152 : (¬ p7))
    (h13408 : (¬ p2) ∨ (¬ p5) ∨ p7 ∨ (¬ p89) ∨ (¬ p228) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p576) ∨ (¬ p1273) ∨ (¬ p1495)) : (¬ p2) ∨ (¬ p5) ∨ (¬ p89) ∨ (¬ p228) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p576) ∨ (¬ p1273) ∨ (¬ p1495) := by
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
  have u2 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h13408 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u9 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step18236 (p7 p12 p110 p124 p961 p1079 : Prop)
    (h16152 : (¬ p7))
    (h13409 : p7 ∨ (¬ p12) ∨ (¬ p110) ∨ (¬ p124) ∨ (¬ p961) ∨ (¬ p1079)) : (¬ p12) ∨ (¬ p110) ∨ (¬ p124) ∨ (¬ p961) ∨ (¬ p1079) := by
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
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1079 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13409 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18237 (p2 p7 p38 p49 p85 p419 p595 p1334 p1542 : Prop)
    (h16152 : (¬ p7))
    (h13410 : (¬ p2) ∨ p7 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p419) ∨ (¬ p595) ∨ (¬ p1334) ∨ (¬ p1542)) : (¬ p2) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p419) ∨ (¬ p595) ∨ (¬ p1334) ∨ (¬ p1542) := by
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
  have u2 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p85 := by
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
  have u6 : p1334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13410 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18238 (p5 p7 p12 p63 p110 p288 p556 p581 p1055 : Prop)
    (h16152 : (¬ p7))
    (h13412 : (¬ p5) ∨ p7 ∨ (¬ p12) ∨ (¬ p63) ∨ (¬ p110) ∨ (¬ p288) ∨ (¬ p556) ∨ (¬ p581) ∨ (¬ p1055)) : (¬ p5) ∨ (¬ p12) ∨ (¬ p63) ∨ (¬ p110) ∨ (¬ p288) ∨ (¬ p556) ∨ (¬ p581) ∨ (¬ p1055) := by
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
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p556 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13412 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18239 (p7 p11 p41 p42 p227 p576 p658 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16199 : (¬ p658))
    (h13413 : p7 ∨ (¬ p11) ∨ (¬ p41) ∨ (¬ p42) ∨ (¬ p227) ∨ (¬ p576) ∨ p658) : (¬ p11) ∨ (¬ p41) ∨ (¬ p227) ∨ (¬ p576) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p227 := by
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
  have u6 : (¬ p658) := by
    exact h16199
  rcases h13413 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step18240 (p5 p7 p63 p860 p1159 p1273 p1333 p1465 : Prop)
    (h16152 : (¬ p7))
    (h13414 : (¬ p5) ∨ p7 ∨ (¬ p63) ∨ (¬ p860) ∨ (¬ p1159) ∨ (¬ p1273) ∨ (¬ p1333) ∨ (¬ p1465)) : (¬ p5) ∨ (¬ p63) ∨ (¬ p860) ∨ (¬ p1159) ∨ (¬ p1273) ∨ (¬ p1333) ∨ (¬ p1465) := by
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
  have u2 : p860 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1273 := by
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
  rcases h13414 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18241 (p7 p12 p110 p160 p532 p1057 p1078 : Prop)
    (h16152 : (¬ p7))
    (h13415 : p7 ∨ (¬ p12) ∨ (¬ p110) ∨ (¬ p160) ∨ (¬ p532) ∨ (¬ p1057) ∨ (¬ p1078)) : (¬ p12) ∨ (¬ p110) ∨ (¬ p160) ∨ (¬ p532) ∨ (¬ p1057) ∨ (¬ p1078) := by
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
  have u2 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1057 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1078 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h13415 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step18242 (p7 p362 p420 p455 p658 p1386 p1452 : Prop)
    (h16152 : (¬ p7))
    (h16199 : (¬ p658))
    (h8348 : p1386)
    (h13416 : p7 ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p455) ∨ p658 ∨ (¬ p1386) ∨ (¬ p1452)) : (¬ p362) ∨ (¬ p420) ∨ (¬ p455) ∨ (¬ p1452) := by
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
  rcases h13416 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step18243 (p7 p12 p41 p42 p89 p225 p256 p426 p576 p1055 p1103 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16178 : (¬ p426))
    (h13417 : p7 ∨ (¬ p12) ∨ (¬ p41) ∨ (¬ p42) ∨ (¬ p89) ∨ (¬ p225) ∨ (¬ p256) ∨ p426 ∨ (¬ p576) ∨ (¬ p1055) ∨ (¬ p1103)) : (¬ p12) ∨ (¬ p41) ∨ (¬ p89) ∨ (¬ p225) ∨ (¬ p256) ∨ (¬ p576) ∨ (¬ p1055) ∨ (¬ p1103) := by
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
  have u2 : p89 := by
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
  have u5 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p42 := by
    exact h132
  have u10 : (¬ p426) := by
    exact h16178
  rcases h13417 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step18244 (p5 p7 p225 p226 p303 p347 p595 p1286 : Prop)
    (h16152 : (¬ p7))
    (h13418 : (¬ p5) ∨ p7 ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p303) ∨ (¬ p347) ∨ (¬ p595) ∨ (¬ p1286)) : (¬ p5) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p303) ∨ (¬ p347) ∨ (¬ p595) ∨ (¬ p1286) := by
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
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p347 := by
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
  rcases h13418 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18245 (p2 p3 p7 p42 p167 p302 p419 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16285 : (¬ p302))
    (h13420 : (¬ p2) ∨ (¬ p3) ∨ p7 ∨ (¬ p42) ∨ (¬ p167) ∨ p302 ∨ (¬ p419)) : (¬ p2) ∨ (¬ p3) ∨ (¬ p167) ∨ (¬ p419) := by
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
  have u2 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p42 := by
    exact h132
  have u6 : (¬ p302) := by
    exact h16285
  rcases h13420 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u4 q2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step18246 (p7 p345 p368 p438 p687 p961 p1080 : Prop)
    (h16152 : (¬ p7))
    (h13421 : p7 ∨ (¬ p345) ∨ (¬ p368) ∨ (¬ p438) ∨ (¬ p687) ∨ (¬ p961) ∨ (¬ p1080)) : (¬ p345) ∨ (¬ p368) ∨ (¬ p438) ∨ (¬ p687) ∨ (¬ p961) ∨ (¬ p1080) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p345 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1080 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h13421 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step18247 (p7 p63 p126 p427 p581 p1232 p1532 : Prop)
    (h16152 : (¬ p7))
    (h2334 : p427)
    (h16398 : (¬ p1532))
    (h13422 : p7 ∨ (¬ p63) ∨ (¬ p126) ∨ (¬ p427) ∨ (¬ p581) ∨ (¬ p1232) ∨ p1532) : (¬ p63) ∨ (¬ p126) ∨ (¬ p581) ∨ (¬ p1232) := by
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
  have u2 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p427 := by
    exact h2334
  have u6 : (¬ p1532) := by
    exact h16398
  rcases h13422 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step18249 (p2 p5 p7 p419 p499 p633 p665 p1077 : Prop)
    (h16152 : (¬ p7))
    (h13425 : (¬ p2) ∨ (¬ p5) ∨ p7 ∨ (¬ p419) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p665) ∨ (¬ p1077)) : (¬ p2) ∨ (¬ p5) ∨ (¬ p419) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p665) ∨ (¬ p1077) := by
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
  have u3 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13425 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18250 (p2 p5 p7 p63 p126 p419 p427 p581 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h2334 : p427)
    (h16309 : (¬ p1324))
    (h13426 : (¬ p2) ∨ (¬ p5) ∨ p7 ∨ (¬ p63) ∨ (¬ p126) ∨ (¬ p419) ∨ (¬ p427) ∨ (¬ p581) ∨ p1324 ∨ (¬ p1325)) : (¬ p2) ∨ (¬ p5) ∨ (¬ p63) ∨ (¬ p126) ∨ (¬ p419) ∨ (¬ p581) ∨ (¬ p1325) := by
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
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p581 := by
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
  rcases h13426 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u5)
  · exact False.elim (u9 q8)
  · exact False.elim (q9 u6)

theorem step18253 (p7 p41 p42 p102 p257 p265 p304 p576 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16170 : (¬ p257))
    (h13429 : p7 ∨ (¬ p41) ∨ (¬ p42) ∨ (¬ p102) ∨ p257 ∨ (¬ p265) ∨ (¬ p304) ∨ (¬ p576)) : (¬ p41) ∨ (¬ p102) ∨ (¬ p265) ∨ (¬ p304) ∨ (¬ p576) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p42 := by
    exact h132
  have u7 : (¬ p257) := by
    exact h16170
  rcases h13429 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (u7 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step18254 (p7 p41 p42 p101 p207 p362 p420 p575 p686 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16205 : (¬ p686))
    (h13430 : p7 ∨ (¬ p41) ∨ (¬ p42) ∨ (¬ p101) ∨ (¬ p207) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p575) ∨ p686) : (¬ p41) ∨ (¬ p101) ∨ (¬ p207) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p575) := by
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
  have u2 : p207 := by
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
  have u7 : p42 := by
    exact h132
  have u8 : (¬ p686) := by
    exact h16205
  rcases h13430 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (u8 q8)

theorem step18255 (p2 p7 p45 p192 p435 p792 p983 p1095 p1096 p1136 p1335 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16259 : (¬ p1136))
    (h13433 : (¬ p2) ∨ p7 ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p435) ∨ (¬ p792) ∨ (¬ p983) ∨ (¬ p1095) ∨ (¬ p1096) ∨ p1136 ∨ (¬ p1335)) : (¬ p2) ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p435) ∨ (¬ p983) ∨ (¬ p1095) ∨ (¬ p1096) ∨ (¬ p1335) := by
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
  have u3 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p983 := by
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
  have u7 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p792 := by
    exact h4535
  have u10 : (¬ p1136) := by
    exact h16259
  rcases h13433 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (u10 q9)
  · exact False.elim (q10 u7)

theorem step18256 (p7 p124 p344 p496 p545 p616 p996 p1287 : Prop)
    (h16152 : (¬ p7))
    (h13434 : p7 ∨ (¬ p124) ∨ (¬ p344) ∨ (¬ p496) ∨ (¬ p545) ∨ (¬ p616) ∨ (¬ p996) ∨ (¬ p1287)) : (¬ p124) ∨ (¬ p344) ∨ (¬ p496) ∨ (¬ p545) ∨ (¬ p616) ∨ (¬ p996) ∨ (¬ p1287) := by
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
  have u2 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13434 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18257 (p7 p138 p382 p576 p797 p819 p1286 p1392 : Prop)
    (h16152 : (¬ p7))
    (h13435 : p7 ∨ (¬ p138) ∨ (¬ p382) ∨ (¬ p576) ∨ (¬ p797) ∨ (¬ p819) ∨ (¬ p1286) ∨ (¬ p1392)) : (¬ p138) ∨ (¬ p382) ∨ (¬ p576) ∨ (¬ p797) ∨ (¬ p819) ∨ (¬ p1286) ∨ (¬ p1392) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p797 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p819 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1392 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13435 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18258 (p7 p18 p42 p193 p257 p423 p1253 p1349 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16170 : (¬ p257))
    (h13436 : p7 ∨ (¬ p18) ∨ (¬ p42) ∨ (¬ p193) ∨ p257 ∨ (¬ p423) ∨ (¬ p1253) ∨ (¬ p1349)) : (¬ p18) ∨ (¬ p193) ∨ (¬ p423) ∨ (¬ p1253) ∨ (¬ p1349) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1253 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p42 := by
    exact h132
  have u7 : (¬ p257) := by
    exact h16170
  rcases h13436 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (u7 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step18259 (p7 p8 p41 p156 p158 p897 p922 : Prop)
    (h16152 : (¬ p7))
    (h13437 : p7 ∨ (¬ p8) ∨ (¬ p41) ∨ (¬ p156) ∨ (¬ p158) ∨ (¬ p897) ∨ (¬ p922)) : (¬ p8) ∨ (¬ p41) ∨ (¬ p156) ∨ (¬ p158) ∨ (¬ p897) ∨ (¬ p922) := by
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
  have u2 : p156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p922 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h13437 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step18260 (p7 p227 p331 p382 p456 p498 p601 p621 p996 : Prop)
    (h16152 : (¬ p7))
    (h13439 : p7 ∨ (¬ p227) ∨ (¬ p331) ∨ (¬ p382) ∨ (¬ p456) ∨ (¬ p498) ∨ (¬ p601) ∨ (¬ p621) ∨ (¬ p996)) : (¬ p227) ∨ (¬ p331) ∨ (¬ p382) ∨ (¬ p456) ∨ (¬ p498) ∨ (¬ p601) ∨ (¬ p621) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p331 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p382 := by
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
  have u5 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p621 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13439 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18261 (p2 p7 p45 p124 p192 p228 p419 p455 p636 p658 p792 : Prop)
    (h16152 : (¬ p7))
    (h16199 : (¬ p658))
    (h4535 : p792)
    (h13440 : (¬ p2) ∨ p7 ∨ (¬ p45) ∨ (¬ p124) ∨ (¬ p192) ∨ (¬ p228) ∨ (¬ p419) ∨ (¬ p455) ∨ (¬ p636) ∨ p658 ∨ (¬ p792)) : (¬ p2) ∨ (¬ p45) ∨ (¬ p124) ∨ (¬ p192) ∨ (¬ p228) ∨ (¬ p419) ∨ (¬ p455) ∨ (¬ p636) := by
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
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p658) := by
    exact h16199
  have u10 : p792 := by
    exact h4535
  rcases h13440 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (u9 q9)
  · exact False.elim (q10 u10)

theorem step18263 (p7 p45 p192 p302 p792 p1159 p1333 p1465 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h4535 : p792)
    (h13442 : p7 ∨ (¬ p45) ∨ (¬ p192) ∨ p302 ∨ (¬ p792) ∨ (¬ p1159) ∨ (¬ p1333) ∨ (¬ p1465)) : (¬ p45) ∨ (¬ p192) ∨ (¬ p1159) ∨ (¬ p1333) ∨ (¬ p1465) := by
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
  have u2 : p1159 := by
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
  have u6 : (¬ p302) := by
    exact h16285
  have u7 : p792 := by
    exact h4535
  rcases h13442 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step18264 (p7 p45 p124 p192 p455 p636 p658 p792 p1035 p1163 p1214 p1226 : Prop)
    (h16152 : (¬ p7))
    (h16199 : (¬ p658))
    (h4535 : p792)
    (h13443 : p7 ∨ (¬ p45) ∨ (¬ p124) ∨ (¬ p192) ∨ (¬ p455) ∨ (¬ p636) ∨ p658 ∨ (¬ p792) ∨ (¬ p1035) ∨ (¬ p1163) ∨ (¬ p1214) ∨ (¬ p1226)) : (¬ p45) ∨ (¬ p124) ∨ (¬ p192) ∨ (¬ p455) ∨ (¬ p636) ∨ (¬ p1035) ∨ (¬ p1163) ∨ (¬ p1214) ∨ (¬ p1226) := by
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
  have u2 : p192 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1214 := by
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
  rcases h13443 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u10 q6)
  · exact False.elim (q7 u11)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step18266 (p7 p45 p193 p792 p980 p1124 p1136 p1225 p1229 p1349 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16259 : (¬ p1136))
    (h13445 : p7 ∨ (¬ p45) ∨ (¬ p193) ∨ (¬ p792) ∨ (¬ p980) ∨ (¬ p1124) ∨ p1136 ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1349)) : (¬ p45) ∨ (¬ p193) ∨ (¬ p980) ∨ (¬ p1124) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1349) := by
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
  have u2 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1124 := by
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
  rcases h13445 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u9 q6)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)

theorem step18267 (p7 p17 p45 p123 p193 p876 p1393 : Prop)
    (h16152 : (¬ p7))
    (h16186 : (¬ p123))
    (h5054 : p876)
    (h13446 : p7 ∨ (¬ p17) ∨ (¬ p45) ∨ p123 ∨ (¬ p193) ∨ (¬ p876) ∨ (¬ p1393)) : (¬ p17) ∨ (¬ p45) ∨ (¬ p193) ∨ (¬ p1393) := by
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
  have u2 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p123) := by
    exact h16186
  have u6 : p876 := by
    exact h5054
  rcases h13446 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step18268 (p7 p45 p192 p302 p419 p477 p690 p792 p1366 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h4535 : p792)
    (h13447 : p7 ∨ (¬ p45) ∨ (¬ p192) ∨ p302 ∨ (¬ p419) ∨ (¬ p477) ∨ (¬ p690) ∨ (¬ p792) ∨ (¬ p1366)) : (¬ p45) ∨ (¬ p192) ∨ (¬ p419) ∨ (¬ p477) ∨ (¬ p690) ∨ (¬ p1366) := by
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
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p477 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p302) := by
    exact h16285
  have u8 : p792 := by
    exact h4535
  rcases h13447 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u7 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u5)

theorem step18270 (p7 p161 p302 p595 p1232 p1333 p1664 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h10244 : p1664)
    (h13449 : p7 ∨ (¬ p161) ∨ p302 ∨ (¬ p595) ∨ (¬ p1232) ∨ (¬ p1333) ∨ (¬ p1664)) : (¬ p161) ∨ (¬ p595) ∨ (¬ p1232) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1232 := by
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
  have u6 : p1664 := by
    exact h10244
  rcases h13449 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step18273 (p7 p43 p90 p193 p424 p1187 : Prop)
    (h16152 : (¬ p7))
    (h13454 : p7 ∨ (¬ p43) ∨ (¬ p90) ∨ (¬ p193) ∨ (¬ p424) ∨ (¬ p1187)) : (¬ p43) ∨ (¬ p90) ∨ (¬ p193) ∨ (¬ p424) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p43 := by
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
  rcases h13454 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18274 (p7 p110 p229 p423 p1041 p1076 : Prop)
    (h16152 : (¬ p7))
    (h13455 : p7 ∨ (¬ p110) ∨ (¬ p229) ∨ (¬ p423) ∨ (¬ p1041) ∨ (¬ p1076)) : (¬ p110) ∨ (¬ p229) ∨ (¬ p423) ∨ (¬ p1041) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1041 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13455 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18275 (p7 p45 p90 p126 p192 p256 p331 p382 p477 p996 : Prop)
    (h16152 : (¬ p7))
    (h13456 : p7 ∨ (¬ p45) ∨ (¬ p90) ∨ (¬ p126) ∨ (¬ p192) ∨ (¬ p256) ∨ (¬ p331) ∨ (¬ p382) ∨ (¬ p477) ∨ (¬ p996)) : (¬ p45) ∨ (¬ p90) ∨ (¬ p126) ∨ (¬ p192) ∨ (¬ p256) ∨ (¬ p331) ∨ (¬ p382) ∨ (¬ p477) ∨ (¬ p996) := by
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
  have u2 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p331 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p477 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h13456 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18276 (p2 p7 p45 p192 p419 p792 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16309 : (¬ p1324))
    (h13457 : (¬ p2) ∨ p7 ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p419) ∨ (¬ p792) ∨ p1324 ∨ (¬ p1325)) : (¬ p2) ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p419) ∨ (¬ p1325) := by
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
  have u3 : p419 := by
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
  rcases h13457 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (u7 q6)
  · exact False.elim (q7 u4)

theorem step18277 (p7 p89 p256 p382 p576 p621 p800 p996 p1393 : Prop)
    (h16152 : (¬ p7))
    (h13460 : p7 ∨ (¬ p89) ∨ (¬ p256) ∨ (¬ p382) ∨ (¬ p576) ∨ (¬ p621) ∨ (¬ p800) ∨ (¬ p996) ∨ (¬ p1393)) : (¬ p89) ∨ (¬ p256) ∨ (¬ p382) ∨ (¬ p576) ∨ (¬ p621) ∨ (¬ p800) ∨ (¬ p996) ∨ (¬ p1393) := by
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
  have u2 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p621 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p800 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13460 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18279 (p256 p791 p1491 p1497 : Prop)
    (h16213 : (¬ p791))
    (h9051 : p1491)
    (h13462 : (¬ p256) ∨ p791 ∨ (¬ p1491) ∨ p1497) : (¬ p256) ∨ p1497 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1497) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p791) := by
    exact h16213
  have u3 : p1491 := by
    exact h9051
  rcases h13462 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (u1 q3)

theorem step18280 (p7 p12 p45 p192 p225 p426 p556 p792 p1055 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h4535 : p792)
    (h13463 : p7 ∨ (¬ p12) ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p225) ∨ p426 ∨ (¬ p556) ∨ (¬ p792) ∨ (¬ p1055)) : (¬ p12) ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p225) ∨ (¬ p556) ∨ (¬ p1055) := by
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
  have u2 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p225 := by
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
  have u7 : (¬ p426) := by
    exact h16178
  have u8 : p792 := by
    exact h4535
  rcases h13463 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u7 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u5)

theorem step18281 (p7 p45 p124 p192 p331 p382 p477 p498 p601 p636 p792 p996 p1136 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16259 : (¬ p1136))
    (h13464 : p7 ∨ (¬ p45) ∨ (¬ p124) ∨ (¬ p192) ∨ (¬ p331) ∨ (¬ p382) ∨ (¬ p477) ∨ (¬ p498) ∨ (¬ p601) ∨ (¬ p636) ∨ (¬ p792) ∨ (¬ p996) ∨ p1136) : (¬ p45) ∨ (¬ p124) ∨ (¬ p192) ∨ (¬ p331) ∨ (¬ p382) ∨ (¬ p477) ∨ (¬ p498) ∨ (¬ p601) ∨ (¬ p636) ∨ (¬ p996) := by
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
  have u2 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p331 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p477 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  have u11 : p792 := by
    exact h4535
  have u12 : (¬ p1136) := by
    exact h16259
  rcases h13464 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
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
  · exact False.elim (q10 u11)
  · exact False.elim (q11 u9)
  · exact False.elim (u12 q12)

theorem step18282 (p7 p42 p185 p193 p534 p653 p1584 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16194 : (¬ p653))
    (h13465 : p7 ∨ (¬ p42) ∨ (¬ p185) ∨ (¬ p193) ∨ (¬ p534) ∨ p653 ∨ (¬ p1584)) : (¬ p185) ∨ (¬ p193) ∨ (¬ p534) ∨ (¬ p1584) := by
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
  have u2 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p42 := by
    exact h132
  have u6 : (¬ p653) := by
    exact h16194
  rcases h13465 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step18283 (p42 p538 p653 p796 : Prop)
    (h132 : p42)
    (h16194 : (¬ p653))
    (h13466 : (¬ p42) ∨ p538 ∨ p653 ∨ (¬ p796)) : p538 ∨ (¬ p796) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p538) := fun hu => hn (Or.inl hu)
  have u1 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p42 := by
    exact h132
  have u3 : (¬ p653) := by
    exact h16194
  rcases h13466 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (u0 q1)
  · exact False.elim (u3 q2)
  · exact False.elim (q3 u1)

theorem step18284 (p7 p156 p343 p344 p419 p537 p726 p796 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16309 : (¬ p1324))
    (h13467 : p7 ∨ (¬ p156) ∨ (¬ p343) ∨ (¬ p344) ∨ (¬ p419) ∨ (¬ p537) ∨ (¬ p726) ∨ (¬ p796) ∨ p1324 ∨ (¬ p1325)) : (¬ p156) ∨ (¬ p344) ∨ (¬ p419) ∨ (¬ p537) ∨ (¬ p726) ∨ (¬ p796) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p796 := by
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
  rcases h13467 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18285 (p7 p45 p193 p430 p792 p814 p1015 : Prop)
    (h16152 : (¬ p7))
    (h16180 : (¬ p430))
    (h4535 : p792)
    (h13468 : p7 ∨ (¬ p45) ∨ (¬ p193) ∨ p430 ∨ (¬ p792) ∨ (¬ p814) ∨ (¬ p1015)) : (¬ p45) ∨ (¬ p193) ∨ (¬ p814) ∨ (¬ p1015) := by
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
  rcases h13468 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step18286 (p7 p42 p193 p302 p1253 p1333 p1349 p1465 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16285 : (¬ p302))
    (h13469 : p7 ∨ (¬ p42) ∨ (¬ p193) ∨ p302 ∨ (¬ p1253) ∨ (¬ p1333) ∨ (¬ p1349) ∨ (¬ p1465)) : (¬ p193) ∨ (¬ p1253) ∨ (¬ p1333) ∨ (¬ p1349) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1253 := by
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
  have u4 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p42 := by
    exact h132
  have u7 : (¬ p302) := by
    exact h16285
  rcases h13469 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (u7 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step18287 (p7 p12 p168 p928 p1118 p1249 : Prop)
    (h16152 : (¬ p7))
    (h13470 : p7 ∨ (¬ p12) ∨ (¬ p168) ∨ (¬ p928) ∨ (¬ p1118) ∨ (¬ p1249)) : (¬ p12) ∨ (¬ p168) ∨ (¬ p928) ∨ (¬ p1118) ∨ (¬ p1249) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p168 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1118 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13470 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18288 (p5 p7 p419 p499 p543 p556 p710 p1325 p1449 p1611 : Prop)
    (h16152 : (¬ p7))
    (h13472 : (¬ p5) ∨ p7 ∨ (¬ p419) ∨ (¬ p499) ∨ (¬ p543) ∨ (¬ p556) ∨ (¬ p710) ∨ (¬ p1325) ∨ (¬ p1449) ∨ (¬ p1611)) : (¬ p5) ∨ (¬ p419) ∨ (¬ p499) ∨ (¬ p543) ∨ (¬ p556) ∨ (¬ p710) ∨ (¬ p1325) ∨ (¬ p1449) ∨ (¬ p1611) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p543 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1449 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1611 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h13472 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18289 (p7 p45 p193 p792 p1253 p1324 p1349 p1465 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16309 : (¬ p1324))
    (h13473 : p7 ∨ (¬ p45) ∨ (¬ p193) ∨ (¬ p792) ∨ (¬ p1253) ∨ p1324 ∨ (¬ p1349) ∨ (¬ p1465)) : (¬ p45) ∨ (¬ p193) ∨ (¬ p1253) ∨ (¬ p1349) ∨ (¬ p1465) := by
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
  have u2 : p1253 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1349 := by
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
  rcases h13473 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u2)
  · exact False.elim (u7 q5)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step18293 (p128 p257 p330 p1187 : Prop)
    (h653 : p128)
    (h16170 : (¬ p257))
    (h13482 : (¬ p128) ∨ p257 ∨ p330 ∨ (¬ p1187)) : p330 ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p330) := fun hu => hn (Or.inl hu)
  have u1 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p128 := by
    exact h653
  have u3 : (¬ p257) := by
    exact h16170
  rcases h13482 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (u3 q1)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u1)

theorem step18294 (p7 p90 p266 p301 p362 p576 : Prop)
    (h16152 : (¬ p7))
    (h13484 : p7 ∨ (¬ p90) ∨ (¬ p266) ∨ (¬ p301) ∨ (¬ p362) ∨ (¬ p576)) : (¬ p90) ∨ (¬ p266) ∨ (¬ p301) ∨ (¬ p362) ∨ (¬ p576) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p90 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13484 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18295 (p7 p288 p520 p575 p636 p1393 : Prop)
    (h16152 : (¬ p7))
    (h13485 : p7 ∨ (¬ p288) ∨ (¬ p520) ∨ (¬ p575) ∨ (¬ p636) ∨ (¬ p1393)) : (¬ p288) ∨ (¬ p520) ∨ (¬ p575) ∨ (¬ p636) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p520 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p575 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13485 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18296 (p3 p7 p41 p166 p195 p283 p576 : Prop)
    (h16152 : (¬ p7))
    (h13489 : (¬ p3) ∨ p7 ∨ (¬ p41) ∨ (¬ p166) ∨ (¬ p195) ∨ (¬ p283) ∨ (¬ p576)) : (¬ p3) ∨ (¬ p41) ∨ (¬ p166) ∨ (¬ p195) ∨ (¬ p283) ∨ (¬ p576) := by
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
  have u2 : p166 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p283 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h13489 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step18298 (p7 p17 p123 p427 p438 p790 p1022 : Prop)
    (h16152 : (¬ p7))
    (h16186 : (¬ p123))
    (h2334 : p427)
    (h13491 : p7 ∨ (¬ p17) ∨ p123 ∨ (¬ p427) ∨ (¬ p438) ∨ (¬ p790) ∨ (¬ p1022)) : (¬ p17) ∨ (¬ p438) ∨ (¬ p790) ∨ (¬ p1022) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p438 := by
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
  have u5 : (¬ p123) := by
    exact h16186
  have u6 : p427 := by
    exact h2334
  rcases h13491 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step18300 (p7 p12 p110 p456 p633 p1079 : Prop)
    (h16152 : (¬ p7))
    (h13493 : p7 ∨ (¬ p12) ∨ (¬ p110) ∨ (¬ p456) ∨ (¬ p633) ∨ (¬ p1079)) : (¬ p12) ∨ (¬ p110) ∨ (¬ p456) ∨ (¬ p633) ∨ (¬ p1079) := by
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
  have u2 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1079 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13493 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18301 (p7 p17 p138 p237 p545 p690 p797 p816 p840 p1366 : Prop)
    (h16152 : (¬ p7))
    (h13496 : p7 ∨ (¬ p17) ∨ (¬ p138) ∨ (¬ p237) ∨ (¬ p545) ∨ (¬ p690) ∨ (¬ p797) ∨ p816 ∨ (¬ p840) ∨ (¬ p1366)) : (¬ p17) ∨ (¬ p138) ∨ (¬ p237) ∨ (¬ p545) ∨ (¬ p690) ∨ (¬ p797) ∨ p816 ∨ (¬ p840) ∨ (¬ p1366) := by
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
  have u4 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p797 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p816) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h13496 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (u6 q7)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step18302 (p7 p237 p261 p289 p961 p1443 : Prop)
    (h16152 : (¬ p7))
    (h13497 : p7 ∨ (¬ p237) ∨ (¬ p261) ∨ (¬ p289) ∨ (¬ p961) ∨ (¬ p1443)) : (¬ p237) ∨ (¬ p261) ∨ (¬ p289) ∨ (¬ p961) ∨ (¬ p1443) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p289 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13497 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18303 (p7 p12 p42 p185 p193 p653 p1115 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16194 : (¬ p653))
    (h13498 : p7 ∨ (¬ p12) ∨ (¬ p42) ∨ (¬ p185) ∨ (¬ p193) ∨ p653 ∨ (¬ p1115)) : (¬ p12) ∨ (¬ p185) ∨ (¬ p193) ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
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
  have u5 : p42 := by
    exact h132
  have u6 : (¬ p653) := by
    exact h16194
  rcases h13498 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step18304 (p7 p8 p69 p419 p728 p1100 p1187 p1334 : Prop)
    (h16152 : (¬ p7))
    (h13499 : p7 ∨ (¬ p8) ∨ (¬ p69) ∨ (¬ p419) ∨ (¬ p728) ∨ (¬ p1100) ∨ (¬ p1187) ∨ (¬ p1334)) : (¬ p8) ∨ (¬ p69) ∨ (¬ p419) ∨ (¬ p728) ∨ (¬ p1100) ∨ (¬ p1187) ∨ (¬ p1334) := by
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
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1100 := by
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
  rcases h13499 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18305 (p7 p17 p69 p123 p419 p434 p518 p790 p1184 p1187 p1334 : Prop)
    (h16152 : (¬ p7))
    (h16186 : (¬ p123))
    (h7053 : p1184)
    (h13500 : p7 ∨ (¬ p17) ∨ (¬ p69) ∨ p123 ∨ (¬ p419) ∨ (¬ p434) ∨ (¬ p518) ∨ (¬ p790) ∨ (¬ p1184) ∨ (¬ p1187) ∨ (¬ p1334)) : (¬ p17) ∨ (¬ p69) ∨ (¬ p419) ∨ (¬ p434) ∨ (¬ p518) ∨ (¬ p790) ∨ (¬ p1187) ∨ (¬ p1334) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p69 := by
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
  have u4 : p518 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p123) := by
    exact h16186
  have u10 : p1184 := by
    exact h7053
  rcases h13500 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step18306 (p7 p41 p138 p262 p310 p922 p1061 p1074 : Prop)
    (h16152 : (¬ p7))
    (h13502 : p7 ∨ (¬ p41) ∨ (¬ p138) ∨ (¬ p262) ∨ (¬ p310) ∨ (¬ p922) ∨ (¬ p1061) ∨ (¬ p1074)) : (¬ p41) ∨ (¬ p138) ∨ (¬ p262) ∨ (¬ p310) ∨ (¬ p922) ∨ (¬ p1061) ∨ (¬ p1074) := by
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
  have u3 : p310 := by
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
  rcases h13502 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18307 (p7 p17 p41 p138 p790 p1385 : Prop)
    (h16152 : (¬ p7))
    (h13503 : p7 ∨ (¬ p17) ∨ (¬ p41) ∨ (¬ p138) ∨ (¬ p790) ∨ (¬ p1385)) : (¬ p17) ∨ (¬ p41) ∨ (¬ p138) ∨ (¬ p790) ∨ (¬ p1385) := by
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
  rcases h13503 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18308 (p7 p63 p286 p344 p545 p621 p690 p928 p1366 : Prop)
    (h16152 : (¬ p7))
    (h13504 : p7 ∨ (¬ p63) ∨ (¬ p286) ∨ (¬ p344) ∨ (¬ p545) ∨ (¬ p621) ∨ (¬ p690) ∨ (¬ p928) ∨ (¬ p1366)) : (¬ p63) ∨ (¬ p286) ∨ (¬ p344) ∨ (¬ p545) ∨ (¬ p621) ∨ (¬ p690) ∨ (¬ p928) ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p286 := by
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
  have u4 : p621 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13504 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18310 (p7 p84 p138 p192 p237 p302 p343 p419 p477 p576 p816 p840 p1015 p1366 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h1950 : p343)
    (h13511 : p7 ∨ (¬ p84) ∨ (¬ p138) ∨ (¬ p192) ∨ (¬ p237) ∨ p302 ∨ (¬ p343) ∨ (¬ p419) ∨ (¬ p477) ∨ (¬ p576) ∨ (¬ p816) ∨ (¬ p840) ∨ (¬ p1015) ∨ (¬ p1366)) : (¬ p84) ∨ (¬ p138) ∨ (¬ p192) ∨ (¬ p237) ∨ (¬ p419) ∨ (¬ p477) ∨ (¬ p576) ∨ (¬ p816) ∨ (¬ p840) ∨ (¬ p1015) ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p477 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p816 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : (¬ p7) := by
    exact h16152
  have u12 : (¬ p302) := by
    exact h16285
  have u13 : p343 := by
    exact h1950
  rcases h13511 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13
  · exact False.elim (u11 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u12 q5)
  · exact False.elim (q6 u13)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)
  · exact False.elim (q12 u9)
  · exact False.elim (q13 u10)

theorem step18312 (p2 p7 p45 p192 p435 p455 p499 p792 p1136 p1335 p1452 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16259 : (¬ p1136))
    (h13513 : (¬ p2) ∨ p7 ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p435) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p792) ∨ p1136 ∨ (¬ p1335) ∨ (¬ p1452)) : (¬ p2) ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p435) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p1335) ∨ (¬ p1452) := by
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
  have u3 : p435 := by
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
  rcases h13513 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u9)
  · exact False.elim (u10 q8)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step18314 (p7 p303 p420 p633 p875 p996 p1075 : Prop)
    (h16152 : (¬ p7))
    (h16220 : (¬ p875))
    (h6478 : p1075)
    (h13516 : p7 ∨ (¬ p303) ∨ (¬ p420) ∨ (¬ p633) ∨ p875 ∨ (¬ p996) ∨ (¬ p1075)) : (¬ p303) ∨ (¬ p420) ∨ (¬ p633) ∨ (¬ p996) := by
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
  have u3 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p875) := by
    exact h16220
  have u6 : p1075 := by
    exact h6478
  rcases h13516 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step18315 (p7 p244 p928 p1061 p1118 p1249 : Prop)
    (h16152 : (¬ p7))
    (h13517 : p7 ∨ (¬ p244) ∨ (¬ p928) ∨ (¬ p1061) ∨ (¬ p1118) ∨ (¬ p1249)) : (¬ p244) ∨ (¬ p928) ∨ (¬ p1061) ∨ (¬ p1118) ∨ (¬ p1249) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p244 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1118 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13517 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18316 (p2 p7 p45 p90 p192 p228 p256 p419 p1443 : Prop)
    (h16152 : (¬ p7))
    (h13518 : (¬ p2) ∨ p7 ∨ (¬ p45) ∨ (¬ p90) ∨ (¬ p192) ∨ (¬ p228) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p1443)) : (¬ p2) ∨ (¬ p45) ∨ (¬ p90) ∨ (¬ p192) ∨ (¬ p228) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p1443) := by
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
  have u4 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p256 := by
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
  rcases h13518 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18317 (p7 p41 p42 p302 p1249 p1333 p1489 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16285 : (¬ p302))
    (h13520 : p7 ∨ (¬ p41) ∨ (¬ p42) ∨ p302 ∨ (¬ p1249) ∨ (¬ p1333) ∨ (¬ p1489)) : (¬ p41) ∨ (¬ p1249) ∨ (¬ p1333) ∨ (¬ p1489) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p42 := by
    exact h132
  have u6 : (¬ p302) := by
    exact h16285
  rcases h13520 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step18318 (p7 p41 p42 p121 p257 p265 p576 p961 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16170 : (¬ p257))
    (h13521 : p7 ∨ (¬ p41) ∨ (¬ p42) ∨ (¬ p121) ∨ p257 ∨ (¬ p265) ∨ (¬ p576) ∨ (¬ p961)) : (¬ p41) ∨ (¬ p121) ∨ (¬ p265) ∨ (¬ p576) ∨ (¬ p961) := by
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
  have u2 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p42 := by
    exact h132
  have u7 : (¬ p257) := by
    exact h16170
  rcases h13521 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (u7 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step18319 (p5 p7 p41 p42 p89 p225 p226 p430 p734 p790 p1385 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16180 : (¬ p430))
    (h13522 : (¬ p5) ∨ p7 ∨ (¬ p41) ∨ (¬ p42) ∨ (¬ p89) ∨ (¬ p225) ∨ (¬ p226) ∨ p430 ∨ (¬ p734) ∨ (¬ p790) ∨ (¬ p1385)) : (¬ p5) ∨ (¬ p41) ∨ (¬ p89) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p734) ∨ (¬ p790) ∨ (¬ p1385) := by
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
  have u2 : p89 := by
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
  have u5 : p734 := by
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
  have u10 : (¬ p430) := by
    exact h16180
  rcases h13522 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u10 q7)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step18320 (p7 p41 p42 p426 p690 p728 p819 p1385 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16178 : (¬ p426))
    (h13523 : p7 ∨ (¬ p41) ∨ (¬ p42) ∨ p426 ∨ (¬ p690) ∨ (¬ p728) ∨ (¬ p819) ∨ (¬ p1385)) : (¬ p41) ∨ (¬ p690) ∨ (¬ p728) ∨ (¬ p819) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p819 := by
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
  have u7 : (¬ p426) := by
    exact h16178
  rcases h13523 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (u7 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step18322 (p7 p41 p42 p256 p576 p1349 p1444 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16406 : (¬ p1444))
    (h13527 : p7 ∨ (¬ p41) ∨ (¬ p42) ∨ (¬ p256) ∨ (¬ p576) ∨ (¬ p1349) ∨ p1444) : (¬ p41) ∨ (¬ p256) ∨ (¬ p576) ∨ (¬ p1349) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
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
  have u3 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p42 := by
    exact h132
  have u6 : (¬ p1444) := by
    exact h16406
  rcases h13527 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step18323 (p7 p41 p163 p164 p791 p1249 p1346 : Prop)
    (h16152 : (¬ p7))
    (h789 : p164)
    (h16213 : (¬ p791))
    (h13528 : p7 ∨ (¬ p41) ∨ (¬ p163) ∨ (¬ p164) ∨ p791 ∨ (¬ p1249) ∨ (¬ p1346)) : (¬ p41) ∨ (¬ p163) ∨ (¬ p1249) ∨ (¬ p1346) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p164 := by
    exact h789
  have u6 : (¬ p791) := by
    exact h16213
  rcases h13528 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step18325 (p7 p41 p42 p382 p819 p875 p996 p1385 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16220 : (¬ p875))
    (h13530 : p7 ∨ (¬ p41) ∨ (¬ p42) ∨ (¬ p382) ∨ (¬ p819) ∨ p875 ∨ (¬ p996) ∨ (¬ p1385)) : (¬ p41) ∨ (¬ p382) ∨ (¬ p819) ∨ (¬ p996) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p819 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p996 := by
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
  have u7 : (¬ p875) := by
    exact h16220
  rcases h13530 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u7 q5)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step18326 (p3 p7 p109 p329 p382 p477 p996 : Prop)
    (h16152 : (¬ p7))
    (h13532 : (¬ p3) ∨ p7 ∨ (¬ p109) ∨ (¬ p329) ∨ (¬ p382) ∨ (¬ p477) ∨ (¬ p996)) : (¬ p3) ∨ (¬ p109) ∨ (¬ p329) ∨ (¬ p382) ∨ (¬ p477) ∨ (¬ p996) := by
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
  have u2 : p329 := by
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
  rcases h13532 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step18327 (p5 p7 p89 p226 p256 p576 p1036 p1120 p1273 : Prop)
    (h16152 : (¬ p7))
    (h13533 : (¬ p5) ∨ p7 ∨ (¬ p89) ∨ (¬ p226) ∨ (¬ p256) ∨ (¬ p576) ∨ (¬ p1036) ∨ (¬ p1120) ∨ (¬ p1273)) : (¬ p5) ∨ (¬ p89) ∨ (¬ p226) ∨ (¬ p256) ∨ (¬ p576) ∨ (¬ p1036) ∨ (¬ p1120) ∨ (¬ p1273) := by
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
  have u3 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1036 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13533 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18328 (p7 p8 p102 p139 p283 p306 p836 : Prop)
    (h16152 : (¬ p7))
    (h13538 : p7 ∨ (¬ p8) ∨ (¬ p102) ∨ (¬ p139) ∨ (¬ p283) ∨ (¬ p306) ∨ (¬ p836)) : (¬ p8) ∨ (¬ p102) ∨ (¬ p139) ∨ (¬ p283) ∨ (¬ p306) ∨ (¬ p836) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
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
  have u3 : p283 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h13538 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step18329 (p4 p7 p110 p124 p125 p544 : Prop)
    (h16152 : (¬ p7))
    (h13539 : (¬ p4) ∨ p7 ∨ (¬ p110) ∨ (¬ p124) ∨ (¬ p125) ∨ (¬ p544)) : (¬ p4) ∨ (¬ p110) ∨ (¬ p124) ∨ (¬ p125) ∨ (¬ p544) := by
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
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13539 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18330 (p5 p7 p63 p125 p206 p323 p1206 p1273 p1490 : Prop)
    (h16152 : (¬ p7))
    (h13540 : (¬ p5) ∨ p7 ∨ (¬ p63) ∨ (¬ p125) ∨ (¬ p206) ∨ (¬ p323) ∨ (¬ p1206) ∨ (¬ p1273) ∨ (¬ p1490)) : (¬ p5) ∨ (¬ p63) ∨ (¬ p125) ∨ (¬ p206) ∨ (¬ p323) ∨ (¬ p1206) ∨ (¬ p1273) ∨ (¬ p1490) := by
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
  rcases h13540 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18331 (p7 p41 p142 p1209 p1249 p1253 : Prop)
    (h16152 : (¬ p7))
    (h13543 : p7 ∨ (¬ p41) ∨ (¬ p142) ∨ (¬ p1209) ∨ (¬ p1249) ∨ (¬ p1253)) : (¬ p41) ∨ (¬ p142) ∨ (¬ p1209) ∨ (¬ p1249) ∨ (¬ p1253) := by
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
  have u2 : p1209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1253 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13543 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18332 (p2 p7 p42 p127 p134 p302 p303 p325 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16285 : (¬ p302))
    (h13544 : (¬ p2) ∨ p7 ∨ (¬ p42) ∨ (¬ p127) ∨ (¬ p134) ∨ p302 ∨ (¬ p303) ∨ (¬ p325)) : (¬ p2) ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p303) ∨ (¬ p325) := by
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
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p42 := by
    exact h132
  have u7 : (¬ p302) := by
    exact h16285
  rcases h13544 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u7 q5)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step18333 (p2 p7 p127 p419 p788 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h5066 : p788)
    (h16309 : (¬ p1324))
    (h13546 : (¬ p2) ∨ p7 ∨ (¬ p127) ∨ (¬ p419) ∨ (¬ p788) ∨ p1324 ∨ (¬ p1325)) : (¬ p2) ∨ (¬ p127) ∨ (¬ p419) ∨ (¬ p1325) := by
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
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p788 := by
    exact h5066
  have u6 : (¬ p1324) := by
    exact h16309
  rcases h13546 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step18334 (p7 p142 p1035 p1209 p1252 p1489 : Prop)
    (h16152 : (¬ p7))
    (h13547 : p7 ∨ (¬ p142) ∨ (¬ p1035) ∨ (¬ p1209) ∨ (¬ p1252) ∨ (¬ p1489)) : (¬ p142) ∨ (¬ p1035) ∨ (¬ p1209) ∨ (¬ p1252) ∨ (¬ p1489) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1252 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13547 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18335 (p5 p6 p7 p10 p63 p303 p860 p1273 : Prop)
    (h16152 : (¬ p7))
    (h13548 : (¬ p5) ∨ (¬ p6) ∨ p7 ∨ (¬ p10) ∨ (¬ p63) ∨ (¬ p303) ∨ (¬ p860) ∨ (¬ p1273)) : (¬ p5) ∨ (¬ p6) ∨ (¬ p10) ∨ (¬ p63) ∨ (¬ p303) ∨ (¬ p860) ∨ (¬ p1273) := by
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
  have u5 : p860 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13548 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18336 (p7 p101 p132 p301 p302 p323 p663 p1076 : Prop)
    (h16152 : (¬ p7))
    (h786 : p132)
    (h16285 : (¬ p302))
    (h13549 : p7 ∨ (¬ p101) ∨ (¬ p132) ∨ (¬ p301) ∨ p302 ∨ (¬ p323) ∨ (¬ p663) ∨ (¬ p1076)) : (¬ p101) ∨ (¬ p301) ∨ (¬ p323) ∨ (¬ p663) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p663 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p132 := by
    exact h786
  have u7 : (¬ p302) := by
    exact h16285
  rcases h13549 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (u7 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step18337 (p7 p101 p285 p323 p348 p836 : Prop)
    (h16152 : (¬ p7))
    (h13550 : p7 ∨ (¬ p101) ∨ (¬ p285) ∨ (¬ p323) ∨ (¬ p348) ∨ (¬ p836)) : (¬ p101) ∨ (¬ p285) ∨ (¬ p323) ∨ (¬ p348) ∨ (¬ p836) := by
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
  have u2 : p323 := by
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
  rcases h13550 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18338 (p7 p132 p301 p329 p438 p1206 p1366 p1445 : Prop)
    (h16152 : (¬ p7))
    (h786 : p132)
    (h16350 : (¬ p1445))
    (h13551 : p7 ∨ (¬ p132) ∨ (¬ p301) ∨ (¬ p329) ∨ (¬ p438) ∨ (¬ p1206) ∨ (¬ p1366) ∨ p1445) : (¬ p301) ∨ (¬ p329) ∨ (¬ p438) ∨ (¬ p1206) ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p329 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p132 := by
    exact h786
  have u7 : (¬ p1445) := by
    exact h16350
  rcases h13551 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u7 q7)

theorem step18340 (p7 p132 p301 p323 p532 p1206 p1324 : Prop)
    (h16152 : (¬ p7))
    (h786 : p132)
    (h16309 : (¬ p1324))
    (h13553 : p7 ∨ (¬ p132) ∨ (¬ p301) ∨ (¬ p323) ∨ (¬ p532) ∨ (¬ p1206) ∨ p1324) : (¬ p301) ∨ (¬ p323) ∨ (¬ p532) ∨ (¬ p1206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p323 := by
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
  have u5 : p132 := by
    exact h786
  have u6 : (¬ p1324) := by
    exact h16309
  rcases h13553 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step18341 (p5 p6 p7 p13 p89 p980 p1206 p1346 p1508 : Prop)
    (h16152 : (¬ p7))
    (h13554 : (¬ p5) ∨ (¬ p6) ∨ p7 ∨ (¬ p13) ∨ (¬ p89) ∨ (¬ p980) ∨ (¬ p1206) ∨ (¬ p1346) ∨ (¬ p1508)) : (¬ p5) ∨ (¬ p6) ∨ (¬ p13) ∨ (¬ p89) ∨ (¬ p980) ∨ (¬ p1206) ∨ (¬ p1346) ∨ (¬ p1508) := by
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
  have u2 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1206 := by
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
  rcases h13554 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u8 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18342 (p2 p5 p7 p89 p237 p435 p983 p1116 p1335 : Prop)
    (h16152 : (¬ p7))
    (h13555 : (¬ p2) ∨ (¬ p5) ∨ p7 ∨ (¬ p89) ∨ (¬ p237) ∨ (¬ p435) ∨ (¬ p983) ∨ (¬ p1116) ∨ (¬ p1335)) : (¬ p2) ∨ (¬ p5) ∨ (¬ p89) ∨ (¬ p237) ∨ (¬ p435) ∨ (¬ p983) ∨ (¬ p1116) ∨ (¬ p1335) := by
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
  have u2 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13555 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u8 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18343 (p7 p89 p125 p139 p237 p323 p500 p581 p918 : Prop)
    (h16152 : (¬ p7))
    (h13556 : p7 ∨ (¬ p89) ∨ (¬ p125) ∨ (¬ p139) ∨ (¬ p237) ∨ (¬ p323) ∨ (¬ p500) ∨ (¬ p581) ∨ (¬ p918)) : (¬ p89) ∨ (¬ p125) ∨ (¬ p139) ∨ (¬ p237) ∨ (¬ p323) ∨ (¬ p500) ∨ (¬ p581) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p89 := by
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
  have u3 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p323 := by
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
  have u7 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13556 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18344 (p7 p41 p42 p686 p918 p1077 p1115 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16205 : (¬ p686))
    (h13557 : p7 ∨ (¬ p41) ∨ (¬ p42) ∨ p686 ∨ (¬ p918) ∨ (¬ p1077) ∨ (¬ p1115)) : (¬ p41) ∨ (¬ p918) ∨ (¬ p1077) ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p42 := by
    exact h132
  have u6 : (¬ p686) := by
    exact h16205
  rcases h13557 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step18345 (p7 p136 p156 p185 p266 p301 p362 : Prop)
    (h16152 : (¬ p7))
    (h13558 : p7 ∨ (¬ p136) ∨ (¬ p156) ∨ (¬ p185) ∨ (¬ p266) ∨ (¬ p301) ∨ (¬ p362)) : (¬ p136) ∨ (¬ p156) ∨ (¬ p185) ∨ (¬ p266) ∨ (¬ p301) ∨ (¬ p362) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p136 := by
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
  have u3 : p266 := by
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
  rcases h13558 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step18346 (p5 p7 p13 p125 p206 p323 p1095 p1096 p1206 : Prop)
    (h16152 : (¬ p7))
    (h13559 : (¬ p5) ∨ p7 ∨ (¬ p13) ∨ (¬ p125) ∨ (¬ p206) ∨ (¬ p323) ∨ (¬ p1095) ∨ (¬ p1096) ∨ (¬ p1206)) : (¬ p5) ∨ (¬ p13) ∨ (¬ p125) ∨ (¬ p206) ∨ (¬ p323) ∨ (¬ p1095) ∨ (¬ p1096) ∨ (¬ p1206) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13559 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18347 (p7 p101 p308 p323 p348 p710 : Prop)
    (h16152 : (¬ p7))
    (h13560 : p7 ∨ (¬ p101) ∨ (¬ p308) ∨ (¬ p323) ∨ (¬ p348) ∨ (¬ p710)) : (¬ p101) ∨ (¬ p308) ∨ (¬ p323) ∨ (¬ p348) ∨ (¬ p710) := by
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
  have u2 : p323 := by
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
  rcases h13560 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18348 (p5 p6 p7 p10 p41 p42 p89 p302 p303 p1249 p1346 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16285 : (¬ p302))
    (h13561 : (¬ p5) ∨ (¬ p6) ∨ p7 ∨ (¬ p10) ∨ (¬ p41) ∨ (¬ p42) ∨ (¬ p89) ∨ p302 ∨ (¬ p303) ∨ (¬ p1249) ∨ (¬ p1346)) : (¬ p5) ∨ (¬ p6) ∨ (¬ p10) ∨ (¬ p41) ∨ (¬ p89) ∨ (¬ p303) ∨ (¬ p1249) ∨ (¬ p1346) := by
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
  have u5 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p42 := by
    exact h132
  have u10 : (¬ p302) := by
    exact h16285
  rcases h13561 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u8 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u4)
  · exact False.elim (u10 q7)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step18349 (p7 p41 p88 p1226 p1251 p1347 p1508 : Prop)
    (h16152 : (¬ p7))
    (h13562 : p7 ∨ (¬ p41) ∨ (¬ p88) ∨ (¬ p1226) ∨ (¬ p1251) ∨ (¬ p1347) ∨ (¬ p1508)) : (¬ p41) ∨ (¬ p88) ∨ (¬ p1226) ∨ (¬ p1251) ∨ (¬ p1347) ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1251 := by
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
  rcases h13562 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step18350 (p5 p6 p7 p10 p41 p42 p159 p160 p161 p430 p438 p1236 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16180 : (¬ p430))
    (h13563 : (¬ p5) ∨ (¬ p6) ∨ p7 ∨ (¬ p10) ∨ (¬ p41) ∨ (¬ p42) ∨ (¬ p159) ∨ (¬ p160) ∨ (¬ p161) ∨ p430 ∨ (¬ p438) ∨ (¬ p1236)) : (¬ p5) ∨ (¬ p6) ∨ (¬ p10) ∨ (¬ p41) ∨ (¬ p159) ∨ (¬ p160) ∨ (¬ p161) ∨ (¬ p438) ∨ (¬ p1236) := by
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
  have u4 : p159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1236 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : p42 := by
    exact h132
  have u11 : (¬ p430) := by
    exact h16180
  rcases h13563 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u9 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (u11 q9)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step18351 (p5 p6 p7 p10 p438 p1225 p1229 p1335 : Prop)
    (h16152 : (¬ p7))
    (h13564 : (¬ p5) ∨ (¬ p6) ∨ p7 ∨ (¬ p10) ∨ (¬ p438) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1335)) : (¬ p5) ∨ (¬ p6) ∨ (¬ p10) ∨ (¬ p438) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1335) := by
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
  rcases h13564 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18352 (p7 p41 p63 p1232 p1251 p1269 : Prop)
    (h16152 : (¬ p7))
    (h13565 : p7 ∨ (¬ p41) ∨ (¬ p63) ∨ (¬ p1232) ∨ (¬ p1251) ∨ (¬ p1269)) : (¬ p41) ∨ (¬ p63) ∨ (¬ p1232) ∨ (¬ p1251) ∨ (¬ p1269) := by
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
  have u2 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1251 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1269 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13565 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18353 (p7 p132 p237 p581 p918 p1349 p1444 : Prop)
    (h16152 : (¬ p7))
    (h786 : p132)
    (h16406 : (¬ p1444))
    (h13566 : p7 ∨ (¬ p132) ∨ (¬ p237) ∨ (¬ p581) ∨ (¬ p918) ∨ (¬ p1349) ∨ p1444) : (¬ p237) ∨ (¬ p581) ∨ (¬ p918) ∨ (¬ p1349) := by
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
  have u2 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p132 := by
    exact h786
  have u6 : (¬ p1444) := by
    exact h16406
  rcases h13566 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step18357 (p5 p6 p7 p10 p303 p665 p1095 p1096 : Prop)
    (h16152 : (¬ p7))
    (h13570 : (¬ p5) ∨ (¬ p6) ∨ p7 ∨ (¬ p10) ∨ (¬ p303) ∨ (¬ p665) ∨ (¬ p1095) ∨ (¬ p1096)) : (¬ p5) ∨ (¬ p6) ∨ (¬ p10) ∨ (¬ p303) ∨ (¬ p665) ∨ (¬ p1095) ∨ (¬ p1096) := by
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
  rcases h13570 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18358 (p5 p6 p7 p9 p10 p41 p42 p302 p303 p922 p1061 p1074 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16285 : (¬ p302))
    (h13571 : (¬ p5) ∨ (¬ p6) ∨ p7 ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p41) ∨ (¬ p42) ∨ p302 ∨ (¬ p303) ∨ (¬ p922) ∨ (¬ p1061) ∨ (¬ p1074)) : (¬ p5) ∨ (¬ p6) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p41) ∨ (¬ p303) ∨ (¬ p922) ∨ (¬ p1061) ∨ (¬ p1074) := by
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
  have u2 : p9 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p922 := by
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
  have u10 : p42 := by
    exact h132
  have u11 : (¬ p302) := by
    exact h16285
  rcases h13571 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u9 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u10)
  · exact False.elim (u11 q7)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step18359 (p7 p156 p160 p185 p1252 p1353 p1489 : Prop)
    (h16152 : (¬ p7))
    (h13572 : p7 ∨ (¬ p156) ∨ (¬ p160) ∨ (¬ p185) ∨ (¬ p1252) ∨ (¬ p1353) ∨ (¬ p1489)) : (¬ p156) ∨ (¬ p160) ∨ (¬ p185) ∨ (¬ p1252) ∨ (¬ p1353) ∨ (¬ p1489) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p156 := by
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
  have u3 : p1252 := by
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
  rcases h13572 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step18360 (p5 p7 p63 p101 p121 p206 p686 p961 p1273 p1386 p1508 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h8348 : p1386)
    (h13573 : (¬ p5) ∨ p7 ∨ (¬ p63) ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p206) ∨ p686 ∨ (¬ p961) ∨ (¬ p1273) ∨ (¬ p1386) ∨ (¬ p1508)) : (¬ p5) ∨ (¬ p63) ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p206) ∨ (¬ p961) ∨ (¬ p1273) ∨ (¬ p1508) := by
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
  have u2 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p961 := by
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
  have u9 : (¬ p686) := by
    exact h16205
  have u10 : p1386 := by
    exact h8348
  rcases h13573 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u9 q6)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u10)
  · exact False.elim (q10 u7)

theorem step18361 (p2 p5 p7 p89 p237 p419 p860 p918 p1273 : Prop)
    (h16152 : (¬ p7))
    (h13574 : (¬ p2) ∨ (¬ p5) ∨ p7 ∨ (¬ p89) ∨ (¬ p237) ∨ (¬ p419) ∨ (¬ p860) ∨ (¬ p918) ∨ (¬ p1273)) : (¬ p2) ∨ (¬ p5) ∨ (¬ p89) ∨ (¬ p237) ∨ (¬ p419) ∨ (¬ p860) ∨ (¬ p918) ∨ (¬ p1273) := by
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
  have u2 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p860 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13574 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u8 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18362 (p2 p5 p7 p419 p533 p1096 p1325 p1562 : Prop)
    (h16152 : (¬ p7))
    (h13576 : (¬ p2) ∨ (¬ p5) ∨ p7 ∨ (¬ p419) ∨ (¬ p533) ∨ (¬ p1096) ∨ (¬ p1325) ∨ (¬ p1562)) : (¬ p2) ∨ (¬ p5) ∨ (¬ p419) ∨ (¬ p533) ∨ (¬ p1096) ∨ (¬ p1325) ∨ (¬ p1562) := by
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
  rcases h13576 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18363 (p7 p41 p156 p537 p922 p1538 : Prop)
    (h16152 : (¬ p7))
    (h13577 : p7 ∨ (¬ p41) ∨ (¬ p156) ∨ (¬ p537) ∨ (¬ p922) ∨ (¬ p1538)) : (¬ p41) ∨ (¬ p156) ∨ (¬ p537) ∨ (¬ p922) ∨ (¬ p1538) := by
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
  have u2 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p922 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1538 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13577 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18364 (p7 p101 p532 p1035 p1084 p1212 : Prop)
    (h16152 : (¬ p7))
    (h13578 : p7 ∨ (¬ p101) ∨ (¬ p532) ∨ (¬ p1035) ∨ (¬ p1084) ∨ (¬ p1212)) : (¬ p101) ∨ (¬ p532) ∨ (¬ p1035) ∨ (¬ p1084) ∨ (¬ p1212) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
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
  have u3 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1212 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13578 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18365 (p7 p132 p301 p362 p959 p1035 p1226 p1484 : Prop)
    (h16152 : (¬ p7))
    (h786 : p132)
    (h16345 : (¬ p1484))
    (h13580 : p7 ∨ (¬ p132) ∨ (¬ p301) ∨ (¬ p362) ∨ (¬ p959) ∨ (¬ p1035) ∨ (¬ p1226) ∨ p1484) : (¬ p301) ∨ (¬ p362) ∨ (¬ p959) ∨ (¬ p1035) ∨ (¬ p1226) := by
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
  have u2 : p959 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p132 := by
    exact h786
  have u7 : (¬ p1484) := by
    exact h16345
  rcases h13580 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u7 q7)

theorem step18366 (p7 p101 p121 p285 p1082 p1115 : Prop)
    (h16152 : (¬ p7))
    (h13581 : p7 ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p285) ∨ (¬ p1082) ∨ (¬ p1115)) : (¬ p101) ∨ (¬ p121) ∨ (¬ p285) ∨ (¬ p1082) ∨ (¬ p1115) := by
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
  have u2 : p285 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1082 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13581 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18367 (p6 p7 p101 p156 p185 p192 p256 p1084 p1443 : Prop)
    (h16152 : (¬ p7))
    (h13582 : (¬ p6) ∨ p7 ∨ (¬ p101) ∨ (¬ p156) ∨ (¬ p185) ∨ (¬ p192) ∨ (¬ p256) ∨ (¬ p1084) ∨ (¬ p1443)) : (¬ p6) ∨ (¬ p101) ∨ (¬ p156) ∨ (¬ p185) ∨ (¬ p192) ∨ (¬ p256) ∨ (¬ p1084) ∨ (¬ p1443) := by
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
  have u5 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13582 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18368 (p7 p11 p136 p156 p185 p227 p266 : Prop)
    (h16152 : (¬ p7))
    (h13583 : p7 ∨ (¬ p11) ∨ (¬ p136) ∨ (¬ p156) ∨ (¬ p185) ∨ (¬ p227) ∨ (¬ p266)) : (¬ p11) ∨ (¬ p136) ∨ (¬ p156) ∨ (¬ p185) ∨ (¬ p227) ∨ (¬ p266) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p136 := by
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
  rcases h13583 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step18370 (p5 p7 p89 p225 p226 p838 p1249 p1346 p1393 : Prop)
    (h16152 : (¬ p7))
    (h13585 : (¬ p5) ∨ p7 ∨ (¬ p89) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p838) ∨ (¬ p1249) ∨ (¬ p1346) ∨ (¬ p1393)) : (¬ p5) ∨ (¬ p89) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p838) ∨ (¬ p1249) ∨ (¬ p1346) ∨ (¬ p1393) := by
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
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p838 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1249 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13585 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18371 (p7 p136 p266 p301 p362 p1251 p1349 : Prop)
    (h16152 : (¬ p7))
    (h13586 : p7 ∨ (¬ p136) ∨ (¬ p266) ∨ (¬ p301) ∨ (¬ p362) ∨ (¬ p1251) ∨ (¬ p1349)) : (¬ p136) ∨ (¬ p266) ∨ (¬ p301) ∨ (¬ p362) ∨ (¬ p1251) ∨ (¬ p1349) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p136 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1251 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h13586 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step18372 (p7 p124 p125 p323 p1075 p1206 p1445 : Prop)
    (h16152 : (¬ p7))
    (h6478 : p1075)
    (h16350 : (¬ p1445))
    (h13587 : p7 ∨ (¬ p124) ∨ (¬ p125) ∨ (¬ p323) ∨ (¬ p1075) ∨ (¬ p1206) ∨ p1445) : (¬ p124) ∨ (¬ p125) ∨ (¬ p323) ∨ (¬ p1206) := by
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
  have u2 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p1075 := by
    exact h6478
  have u6 : (¬ p1445) := by
    exact h16350
  rcases h13587 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step18373 (p7 p42 p124 p125 p136 p258 p302 p303 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16285 : (¬ p302))
    (h13588 : p7 ∨ (¬ p42) ∨ (¬ p124) ∨ (¬ p125) ∨ (¬ p136) ∨ (¬ p258) ∨ p302 ∨ (¬ p303)) : (¬ p124) ∨ (¬ p125) ∨ (¬ p136) ∨ (¬ p258) ∨ (¬ p303) := by
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
  have u2 : p136 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p42 := by
    exact h132
  have u7 : (¬ p302) := by
    exact h16285
  rcases h13588 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u7 q6)
  · exact False.elim (q7 u4)

theorem step18374 (p7 p41 p89 p142 p788 p1136 p1249 p1346 : Prop)
    (h16152 : (¬ p7))
    (h5066 : p788)
    (h16259 : (¬ p1136))
    (h13589 : p7 ∨ (¬ p41) ∨ (¬ p89) ∨ (¬ p142) ∨ (¬ p788) ∨ p1136 ∨ (¬ p1249) ∨ (¬ p1346)) : (¬ p41) ∨ (¬ p89) ∨ (¬ p142) ∨ (¬ p1249) ∨ (¬ p1346) := by
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
  have u2 : p142 := by
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
  have u6 : p788 := by
    exact h5066
  have u7 : (¬ p1136) := by
    exact h16259
  rcases h13589 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)
  · exact False.elim (u7 q5)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step18375 (p7 p10 p102 p302 p303 p304 p681 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h3892 : p681)
    (h13590 : p7 ∨ (¬ p10) ∨ (¬ p102) ∨ p302 ∨ (¬ p303) ∨ (¬ p304) ∨ (¬ p681)) : (¬ p10) ∨ (¬ p102) ∨ (¬ p303) ∨ (¬ p304) := by
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
  have u3 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p302) := by
    exact h16285
  have u6 : p681 := by
    exact h3892
  rcases h13590 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step18376 (p7 p132 p238 p256 p344 p710 p1076 p1181 : Prop)
    (h16152 : (¬ p7))
    (h786 : p132)
    (h16272 : (¬ p1181))
    (h13594 : p7 ∨ (¬ p132) ∨ (¬ p238) ∨ (¬ p256) ∨ (¬ p344) ∨ (¬ p710) ∨ (¬ p1076) ∨ p1181) : (¬ p238) ∨ (¬ p256) ∨ (¬ p344) ∨ (¬ p710) ∨ (¬ p1076) := by
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
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p132 := by
    exact h786
  have u7 : (¬ p1181) := by
    exact h16272
  rcases h13594 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u7 q7)

theorem step18377 (p7 p160 p495 p636 p1040 p1076 p1233 p1465 : Prop)
    (h16152 : (¬ p7))
    (h13596 : p7 ∨ (¬ p160) ∨ (¬ p495) ∨ (¬ p636) ∨ (¬ p1040) ∨ (¬ p1076) ∨ (¬ p1233) ∨ (¬ p1465)) : (¬ p160) ∨ (¬ p495) ∨ (¬ p636) ∨ (¬ p1040) ∨ (¬ p1076) ∨ (¬ p1233) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p160 := by
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
  have u3 : p1040 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1233 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13596 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18378 (p7 p8 p664 p983 p1056 p1226 : Prop)
    (h16152 : (¬ p7))
    (h13597 : p7 ∨ (¬ p8) ∨ (¬ p664) ∨ (¬ p983) ∨ (¬ p1056) ∨ (¬ p1226)) : (¬ p8) ∨ (¬ p664) ∨ (¬ p983) ∨ (¬ p1056) ∨ (¬ p1226) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
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
  have u3 : p1056 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13597 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18379 (p7 p83 p499 p582 p814 p839 p928 : Prop)
    (h16152 : (¬ p7))
    (h13599 : p7 ∨ (¬ p83) ∨ (¬ p499) ∨ (¬ p582) ∨ (¬ p814) ∨ (¬ p839) ∨ (¬ p928)) : (¬ p83) ∨ (¬ p499) ∨ (¬ p582) ∨ (¬ p814) ∨ (¬ p839) ∨ (¬ p928) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p83 := by
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
  have u3 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p839 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h13599 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step18381 (p7 p140 p189 p256 p422 p1209 : Prop)
    (h16152 : (¬ p7))
    (h13601 : p7 ∨ (¬ p140) ∨ (¬ p189) ∨ (¬ p256) ∨ (¬ p422) ∨ (¬ p1209)) : (¬ p140) ∨ (¬ p189) ∨ (¬ p256) ∨ (¬ p422) ∨ (¬ p1209) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p140 := by
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
  have u3 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13601 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18384 (p7 p193 p1226 p1251 p1347 p1508 : Prop)
    (h16152 : (¬ p7))
    (h13608 : p7 ∨ (¬ p193) ∨ (¬ p1226) ∨ (¬ p1251) ∨ (¬ p1347) ∨ (¬ p1508)) : (¬ p193) ∨ (¬ p1226) ∨ (¬ p1251) ∨ (¬ p1347) ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1251 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13608 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18385 (p7 p42 p193 p304 p348 p362 p431 p435 p657 p686 p798 p814 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16205 : (¬ p686))
    (h13609 : p7 ∨ (¬ p42) ∨ (¬ p193) ∨ (¬ p304) ∨ (¬ p348) ∨ (¬ p362) ∨ (¬ p431) ∨ (¬ p435) ∨ (¬ p657) ∨ p686 ∨ (¬ p798) ∨ (¬ p814)) : (¬ p193) ∨ (¬ p304) ∨ (¬ p348) ∨ (¬ p362) ∨ (¬ p431) ∨ (¬ p435) ∨ (¬ p657) ∨ (¬ p798) ∨ (¬ p814) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p193 := by
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
  have u4 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p798 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : p42 := by
    exact h132
  have u11 : (¬ p686) := by
    exact h16205
  rcases h13609 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (u11 q9)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step18386 (p7 p156 p193 p435 p798 p814 p983 p1116 p1335 : Prop)
    (h16152 : (¬ p7))
    (h13610 : p7 ∨ (¬ p156) ∨ (¬ p193) ∨ (¬ p435) ∨ (¬ p798) ∨ (¬ p814) ∨ (¬ p983) ∨ (¬ p1116) ∨ (¬ p1335)) : (¬ p156) ∨ (¬ p193) ∨ (¬ p435) ∨ (¬ p798) ∨ (¬ p814) ∨ (¬ p983) ∨ (¬ p1116) ∨ (¬ p1335) := by
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
  have u2 : p435 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13610 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18387 (p1 p7 p110 p346 p690 p713 p1366 : Prop)
    (h16152 : (¬ p7))
    (h13612 : (¬ p1) ∨ p7 ∨ (¬ p110) ∨ (¬ p346) ∨ (¬ p690) ∨ (¬ p713) ∨ (¬ p1366)) : (¬ p1) ∨ (¬ p110) ∨ (¬ p346) ∨ (¬ p690) ∨ (¬ p713) ∨ (¬ p1366) := by
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
  have u2 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p713 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h13612 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step18388 (p7 p138 p193 p262 p362 p434 p814 p858 p1334 : Prop)
    (h16152 : (¬ p7))
    (h13614 : p7 ∨ (¬ p138) ∨ (¬ p193) ∨ (¬ p262) ∨ (¬ p362) ∨ (¬ p434) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1334)) : (¬ p138) ∨ (¬ p193) ∨ (¬ p262) ∨ (¬ p362) ∨ (¬ p434) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1334) := by
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
  have u3 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p434 := by
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
  have u7 : p1334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13614 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18390 (p7 p290 p918 p1076 p1121 p1273 : Prop)
    (h16152 : (¬ p7))
    (h13616 : p7 ∨ (¬ p290) ∨ (¬ p918) ∨ (¬ p1076) ∨ (¬ p1121) ∨ (¬ p1273)) : (¬ p290) ∨ (¬ p918) ∨ (¬ p1076) ∨ (¬ p1121) ∨ (¬ p1273) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p290 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1076 := by
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
  rcases h13616 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18391 (p7 p8 p230 p262 p310 p581 p657 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h8348 : p1386)
    (h13617 : p7 ∨ (¬ p8) ∨ p230 ∨ (¬ p262) ∨ (¬ p310) ∨ (¬ p581) ∨ (¬ p657) ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p8) ∨ (¬ p262) ∨ (¬ p310) ∨ (¬ p581) ∨ (¬ p657) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p310 := by
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
  have u5 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p230) := by
    exact h16165
  have u8 : p1386 := by
    exact h8348
  rcases h13617 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u8)

theorem step18392 (p7 p814 p1135 p1325 p1346 p1508 p1527 : Prop)
    (h16152 : (¬ p7))
    (h6744 : p1135)
    (h16359 : (¬ p1527))
    (h13619 : p7 ∨ (¬ p814) ∨ (¬ p1135) ∨ (¬ p1325) ∨ (¬ p1346) ∨ (¬ p1508) ∨ p1527) : (¬ p814) ∨ (¬ p1325) ∨ (¬ p1346) ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1325 := by
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
  have u5 : p1135 := by
    exact h6744
  have u6 : (¬ p1527) := by
    exact h16359
  rcases h13619 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step18393 (p7 p45 p193 p387 p499 p601 p792 p864 p1136 p1349 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16259 : (¬ p1136))
    (h13620 : p7 ∨ (¬ p45) ∨ (¬ p193) ∨ (¬ p387) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p792) ∨ (¬ p864) ∨ p1136 ∨ (¬ p1349)) : (¬ p45) ∨ (¬ p193) ∨ (¬ p387) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p864) ∨ (¬ p1349) := by
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
  have u5 : p864 := by
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
  rcases h13620 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u5)
  · exact False.elim (u9 q8)
  · exact False.elim (q9 u6)

theorem step18395 (p7 p346 p904 p1077 p1096 p1136 p1139 : Prop)
    (h16152 : (¬ p7))
    (h16259 : (¬ p1136))
    (h6761 : p1139)
    (h13622 : p7 ∨ (¬ p346) ∨ (¬ p904) ∨ (¬ p1077) ∨ (¬ p1096) ∨ p1136 ∨ (¬ p1139)) : (¬ p346) ∨ (¬ p904) ∨ (¬ p1077) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p904 := by
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
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p1136) := by
    exact h16259
  have u6 : p1139 := by
    exact h6761
  rcases h13622 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)

theorem step18398 (p7 p8 p69 p310 p346 p496 p1044 p1077 p1141 : Prop)
    (h16152 : (¬ p7))
    (h13625 : p7 ∨ (¬ p8) ∨ (¬ p69) ∨ (¬ p310) ∨ (¬ p346) ∨ (¬ p496) ∨ (¬ p1044) ∨ (¬ p1077) ∨ (¬ p1141)) : (¬ p8) ∨ (¬ p69) ∨ (¬ p310) ∨ (¬ p346) ∨ (¬ p496) ∨ (¬ p1044) ∨ (¬ p1077) ∨ (¬ p1141) := by
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
  have u2 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1044 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13625 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18401 (p6 p7 p19 p229 p659 p1036 p1181 : Prop)
    (h16152 : (¬ p7))
    (h3753 : p659)
    (h16272 : (¬ p1181))
    (h13628 : (¬ p6) ∨ p7 ∨ (¬ p19) ∨ (¬ p229) ∨ (¬ p659) ∨ (¬ p1036) ∨ p1181) : (¬ p6) ∨ (¬ p19) ∨ (¬ p229) ∨ (¬ p1036) := by
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
  have u3 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p659 := by
    exact h3753
  have u6 : (¬ p1181) := by
    exact h16272
  rcases h13628 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step18402 (p6 p7 p8 p9 p13 p45 p192 p792 p897 p1095 p1136 p1206 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16259 : (¬ p1136))
    (h13631 : (¬ p6) ∨ p7 ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p13) ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p792) ∨ (¬ p897) ∨ (¬ p1095) ∨ p1136 ∨ (¬ p1206)) : (¬ p6) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p13) ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p897) ∨ (¬ p1095) ∨ (¬ p1206) := by
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
  have u2 : p9 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p192 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : p792 := by
    exact h4535
  have u11 : (¬ p1136) := by
    exact h16259
  rcases h13631 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (q0 u0)
  · exact False.elim (u9 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (u11 q10)
  · exact False.elim (q11 u8)

theorem step18403 (p7 p162 p185 p266 p576 p792 p1631 p1644 : Prop)
    (h16152 : (¬ p7))
    (h16160 : (¬ p162))
    (h4535 : p792)
    (h13632 : p7 ∨ p162 ∨ (¬ p185) ∨ (¬ p266) ∨ (¬ p576) ∨ (¬ p792) ∨ (¬ p1631) ∨ (¬ p1644)) : (¬ p185) ∨ (¬ p266) ∨ (¬ p576) ∨ (¬ p1631) ∨ (¬ p1644) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1631 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1644 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p162) := by
    exact h16160
  have u7 : p792 := by
    exact h4535
  rcases h13632 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step18406 (p7 p45 p101 p192 p206 p686 p792 p1624 p1665 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h4535 : p792)
    (h13638 : p7 ∨ (¬ p45) ∨ (¬ p101) ∨ (¬ p192) ∨ (¬ p206) ∨ p686 ∨ (¬ p792) ∨ (¬ p1624) ∨ (¬ p1665)) : (¬ p45) ∨ (¬ p101) ∨ (¬ p192) ∨ (¬ p206) ∨ (¬ p1624) ∨ (¬ p1665) := by
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
  have u2 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1624 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p686) := by
    exact h16205
  have u8 : p792 := by
    exact h4535
  rcases h13638 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u7 q5)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)

theorem step18407 (p7 p41 p63 p156 p923 p1099 : Prop)
    (h16152 : (¬ p7))
    (h13639 : p7 ∨ (¬ p41) ∨ (¬ p63) ∨ (¬ p156) ∨ (¬ p923) ∨ (¬ p1099)) : (¬ p41) ∨ (¬ p63) ∨ (¬ p156) ∨ (¬ p923) ∨ (¬ p1099) := by
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
  have u2 : p156 := by
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
  rcases h13639 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18412 (p7 p101 p121 p456 p495 p686 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h7053 : p1184)
    (h13645 : p7 ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p456) ∨ (¬ p495) ∨ p686 ∨ (¬ p1184)) : (¬ p101) ∨ (¬ p121) ∨ (¬ p456) ∨ (¬ p495) := by
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
  have u2 : p456 := by
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
  rcases h13645 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)

theorem step18414 (p7 p230 p814 p861 p1333 p1346 p1386 p1393 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h8348 : p1386)
    (h13647 : p7 ∨ p230 ∨ (¬ p814) ∨ (¬ p861) ∨ (¬ p1333) ∨ (¬ p1346) ∨ (¬ p1386) ∨ (¬ p1393)) : (¬ p814) ∨ (¬ p861) ∨ (¬ p1333) ∨ (¬ p1346) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p861 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p230) := by
    exact h16165
  have u7 : p1386 := by
    exact h8348
  rcases h13647 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step18419 (p7 p138 p193 p261 p961 p1443 : Prop)
    (h16152 : (¬ p7))
    (h13655 : p7 ∨ (¬ p138) ∨ (¬ p193) ∨ (¬ p261) ∨ (¬ p961) ∨ (¬ p1443)) : (¬ p138) ∨ (¬ p193) ∨ (¬ p261) ∨ (¬ p961) ∨ (¬ p1443) := by
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
  have u2 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13655 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18420 (p2 p7 p127 p303 p325 p426 p657 p788 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h5066 : p788)
    (h13657 : (¬ p2) ∨ p7 ∨ (¬ p127) ∨ (¬ p303) ∨ (¬ p325) ∨ p426 ∨ (¬ p657) ∨ (¬ p788)) : (¬ p2) ∨ (¬ p127) ∨ (¬ p303) ∨ (¬ p325) ∨ (¬ p657) := by
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
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p426) := by
    exact h16178
  have u7 : p788 := by
    exact h5066
  rcases h13657 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step18421 (p7 p41 p63 p142 p224 p302 p304 p346 p500 p788 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h5066 : p788)
    (h13658 : p7 ∨ (¬ p41) ∨ (¬ p63) ∨ (¬ p142) ∨ (¬ p224) ∨ p302 ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p500) ∨ (¬ p788)) : (¬ p41) ∨ (¬ p63) ∨ (¬ p142) ∨ (¬ p224) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p500) := by
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
  have u3 : p224 := by
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
  have u6 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p302) := by
    exact h16285
  have u9 : p788 := by
    exact h5066
  rcases h13658 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18422 (p7 p42 p134 p210 p224 p302 p304 p346 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16285 : (¬ p302))
    (h13659 : p7 ∨ (¬ p42) ∨ (¬ p134) ∨ (¬ p210) ∨ (¬ p224) ∨ p302 ∨ (¬ p304) ∨ (¬ p346)) : (¬ p134) ∨ (¬ p210) ∨ (¬ p224) ∨ (¬ p304) ∨ (¬ p346) := by
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
  have u6 : p42 := by
    exact h132
  have u7 : (¬ p302) := by
    exact h16285
  rcases h13659 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u7 q5)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step18423 (p7 p41 p42 p166 p225 p344 p686 p918 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16205 : (¬ p686))
    (h13660 : p7 ∨ (¬ p41) ∨ (¬ p42) ∨ (¬ p166) ∨ (¬ p225) ∨ (¬ p344) ∨ p686 ∨ (¬ p918)) : (¬ p41) ∨ (¬ p166) ∨ (¬ p225) ∨ (¬ p344) ∨ (¬ p918) := by
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
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
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
  rcases h13660 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u7 q6)
  · exact False.elim (q7 u4)

theorem step18424 (p7 p41 p42 p125 p159 p160 p161 p323 p500 p1206 p1236 p1445 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16350 : (¬ p1445))
    (h13661 : p7 ∨ (¬ p41) ∨ (¬ p42) ∨ (¬ p125) ∨ (¬ p159) ∨ (¬ p160) ∨ (¬ p161) ∨ (¬ p323) ∨ (¬ p500) ∨ (¬ p1206) ∨ (¬ p1236) ∨ p1445) : (¬ p41) ∨ (¬ p125) ∨ (¬ p159) ∨ (¬ p160) ∨ (¬ p161) ∨ (¬ p323) ∨ (¬ p500) ∨ (¬ p1206) ∨ (¬ p1236) := by
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
  have u2 : p159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1236 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : p42 := by
    exact h132
  have u11 : (¬ p1445) := by
    exact h16350
  rcases h13661 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
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

theorem step18425 (p5 p7 p107 p206 p225 p304 p734 p1225 p1229 p1335 : Prop)
    (h16152 : (¬ p7))
    (h13662 : (¬ p5) ∨ p7 ∨ (¬ p107) ∨ (¬ p206) ∨ (¬ p225) ∨ (¬ p304) ∨ (¬ p734) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1335)) : (¬ p5) ∨ (¬ p107) ∨ (¬ p206) ∨ (¬ p225) ∨ (¬ p304) ∨ (¬ p734) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1335) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p107 := by
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
  have u4 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p734 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h13662 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18426 (p5 p7 p63 p1022 p1159 p1330 p1393 p1465 : Prop)
    (h16152 : (¬ p7))
    (h13663 : (¬ p5) ∨ p7 ∨ (¬ p63) ∨ (¬ p1022) ∨ (¬ p1159) ∨ (¬ p1330) ∨ (¬ p1393) ∨ (¬ p1465)) : (¬ p5) ∨ (¬ p63) ∨ (¬ p1022) ∨ (¬ p1159) ∨ (¬ p1330) ∨ (¬ p1393) ∨ (¬ p1465) := by
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
  have u2 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13663 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18427 (p6 p7 p101 p1084 p1140 p1211 : Prop)
    (h16152 : (¬ p7))
    (h13664 : (¬ p6) ∨ p7 ∨ (¬ p101) ∨ (¬ p1084) ∨ (¬ p1140) ∨ (¬ p1211)) : (¬ p6) ∨ (¬ p101) ∨ (¬ p1084) ∨ (¬ p1140) ∨ (¬ p1211) := by
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
  have u2 : p1084 := by
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
  rcases h13664 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18428 (p7 p8 p69 p728 p1100 p1141 p1330 p1465 : Prop)
    (h16152 : (¬ p7))
    (h13665 : p7 ∨ (¬ p8) ∨ (¬ p69) ∨ (¬ p728) ∨ (¬ p1100) ∨ (¬ p1141) ∨ (¬ p1330) ∨ (¬ p1465)) : (¬ p8) ∨ (¬ p69) ∨ (¬ p728) ∨ (¬ p1100) ∨ (¬ p1141) ∨ (¬ p1330) ∨ (¬ p1465) := by
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
  have u2 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1100 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1141 := by
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
  rcases h13665 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18429 (p7 p8 p18 p69 p101 p657 p686 p1100 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h8348 : p1386)
    (h13666 : p7 ∨ (¬ p8) ∨ (¬ p18) ∨ (¬ p69) ∨ (¬ p101) ∨ (¬ p657) ∨ p686 ∨ (¬ p1100) ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p8) ∨ (¬ p18) ∨ (¬ p69) ∨ (¬ p101) ∨ (¬ p657) ∨ (¬ p1100) ∨ (¬ p1333) := by
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
  have u3 : p101 := by
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
  have u8 : (¬ p686) := by
    exact h16205
  have u9 : p1386 := by
    exact h8348
  rcases h13666 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18430 (p7 p69 p101 p329 p686 p1184 p1188 p1366 p1545 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h7053 : p1184)
    (h13667 : p7 ∨ (¬ p69) ∨ (¬ p101) ∨ (¬ p329) ∨ p686 ∨ (¬ p1184) ∨ (¬ p1188) ∨ (¬ p1366) ∨ (¬ p1545)) : (¬ p69) ∨ (¬ p101) ∨ (¬ p329) ∨ (¬ p1188) ∨ (¬ p1366) ∨ (¬ p1545) := by
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
  have u2 : p329 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p686) := by
    exact h16205
  have u8 : p1184 := by
    exact h7053
  rcases h13667 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u7 q4)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)

theorem step18431 (p7 p16 p101 p134 p189 p455 p499 p1084 : Prop)
    (h16152 : (¬ p7))
    (h13668 : p7 ∨ (¬ p16) ∨ (¬ p101) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p1084)) : (¬ p16) ∨ (¬ p101) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p1084) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p101 := by
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
  have u4 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13668 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18433 (p7 p20 p46 p142 p207 p227 p456 : Prop)
    (h16152 : (¬ p7))
    (h13670 : p7 ∨ (¬ p20) ∨ (¬ p46) ∨ (¬ p142) ∨ (¬ p207) ∨ (¬ p227) ∨ (¬ p456)) : (¬ p20) ∨ (¬ p46) ∨ (¬ p142) ∨ (¬ p207) ∨ (¬ p227) ∨ (¬ p456) := by
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
  rcases h13670 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step18434 (p7 p104 p142 p167 p207 p227 p1084 : Prop)
    (h16152 : (¬ p7))
    (h13671 : p7 ∨ (¬ p104) ∨ (¬ p142) ∨ (¬ p167) ∨ (¬ p207) ∨ (¬ p227) ∨ (¬ p1084)) : (¬ p104) ∨ (¬ p142) ∨ (¬ p167) ∨ (¬ p207) ∨ (¬ p227) ∨ (¬ p1084) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p104 := by
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
  have u3 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h13671 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step18435 (p7 p18 p142 p191 p423 p1159 : Prop)
    (h16152 : (¬ p7))
    (h13672 : p7 ∨ (¬ p18) ∨ (¬ p142) ∨ (¬ p191) ∨ (¬ p423) ∨ (¬ p1159)) : (¬ p18) ∨ (¬ p142) ∨ (¬ p191) ∨ (¬ p423) ∨ (¬ p1159) := by
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
  have u2 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13672 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18436 (p7 p8 p163 p191 p557 p728 p1159 p1330 p1465 : Prop)
    (h16152 : (¬ p7))
    (h13674 : p7 ∨ (¬ p8) ∨ (¬ p163) ∨ (¬ p191) ∨ (¬ p557) ∨ (¬ p728) ∨ (¬ p1159) ∨ (¬ p1330) ∨ (¬ p1465)) : (¬ p8) ∨ (¬ p163) ∨ (¬ p191) ∨ (¬ p557) ∨ (¬ p728) ∨ (¬ p1159) ∨ (¬ p1330) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
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
  have u3 : p557 := by
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
  rcases h13674 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18437 (p7 p16 p188 p228 p455 p499 p1159 p1333 p1465 : Prop)
    (h16152 : (¬ p7))
    (h13675 : p7 ∨ (¬ p16) ∨ (¬ p188) ∨ (¬ p228) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p1159) ∨ (¬ p1333) ∨ (¬ p1465)) : (¬ p16) ∨ (¬ p188) ∨ (¬ p228) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p1159) ∨ (¬ p1333) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p228 := by
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
  have u5 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13675 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18440 (p7 p123 p227 p288 p304 p1386 p1452 : Prop)
    (h16152 : (¬ p7))
    (h16186 : (¬ p123))
    (h8348 : p1386)
    (h13678 : p7 ∨ p123 ∨ (¬ p227) ∨ (¬ p288) ∨ (¬ p304) ∨ (¬ p1386) ∨ (¬ p1452)) : (¬ p227) ∨ (¬ p288) ∨ (¬ p304) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p227 := by
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
  have u3 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p123) := by
    exact h16186
  have u6 : p1386 := by
    exact h8348
  rcases h13678 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step18441 (p7 p264 p286 p304 p576 p928 : Prop)
    (h16152 : (¬ p7))
    (h13680 : p7 ∨ (¬ p264) ∨ (¬ p286) ∨ (¬ p304) ∨ (¬ p576) ∨ (¬ p928)) : (¬ p264) ∨ (¬ p286) ∨ (¬ p304) ∨ (¬ p576) ∨ (¬ p928) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p264 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p286 := by
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
  have u4 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13680 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18442 (p7 p123 p288 p304 p362 p387 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16186 : (¬ p123))
    (h6744 : p1135)
    (h13681 : p7 ∨ p123 ∨ (¬ p288) ∨ (¬ p304) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p1135)) : (¬ p288) ∨ (¬ p304) ∨ (¬ p362) ∨ (¬ p387) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p288 := by
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
  have u5 : (¬ p123) := by
    exact h16186
  have u6 : p1135 := by
    exact h6744
  rcases h13681 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step18443 (p7 p16 p134 p188 p257 p657 p904 p1096 p1135 p1159 p1256 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h6744 : p1135)
    (h13682 : p7 ∨ (¬ p16) ∨ (¬ p134) ∨ (¬ p188) ∨ p257 ∨ (¬ p657) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1135) ∨ (¬ p1159) ∨ (¬ p1256)) : (¬ p16) ∨ (¬ p134) ∨ (¬ p188) ∨ (¬ p657) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1159) ∨ (¬ p1256) := by
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
  have u2 : p188 := by
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
  have u6 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p257) := by
    exact h16170
  have u10 : p1135 := by
    exact h6744
  rcases h13682 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step18444 (p7 p16 p189 p422 p657 p904 p1004 p1096 : Prop)
    (h16152 : (¬ p7))
    (h13683 : p7 ∨ (¬ p16) ∨ (¬ p189) ∨ (¬ p422) ∨ (¬ p657) ∨ (¬ p904) ∨ (¬ p1004) ∨ (¬ p1096)) : (¬ p16) ∨ (¬ p189) ∨ (¬ p422) ∨ (¬ p657) ∨ (¬ p904) ∨ (¬ p1004) ∨ (¬ p1096) := by
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
  have u3 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13683 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18445 (p7 p16 p533 p814 p858 p1096 p1325 p1562 : Prop)
    (h16152 : (¬ p7))
    (h13684 : p7 ∨ (¬ p16) ∨ (¬ p533) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1096) ∨ (¬ p1325) ∨ (¬ p1562)) : (¬ p16) ∨ (¬ p533) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1096) ∨ (¬ p1325) ∨ (¬ p1562) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p533 := by
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
  rcases h13684 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18446 (p7 p16 p189 p422 p533 p1096 p1465 p1562 : Prop)
    (h16152 : (¬ p7))
    (h13686 : p7 ∨ (¬ p16) ∨ (¬ p189) ∨ (¬ p422) ∨ (¬ p533) ∨ (¬ p1096) ∨ (¬ p1465) ∨ (¬ p1562)) : (¬ p16) ∨ (¬ p189) ∨ (¬ p422) ∨ (¬ p533) ∨ (¬ p1096) ∨ (¬ p1465) ∨ (¬ p1562) := by
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
  have u3 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1562 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13686 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18447 (p7 p16 p188 p545 p796 p904 p1096 p1159 p1256 : Prop)
    (h16152 : (¬ p7))
    (h13687 : p7 ∨ (¬ p16) ∨ (¬ p188) ∨ (¬ p545) ∨ (¬ p796) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1159) ∨ (¬ p1256)) : (¬ p16) ∨ (¬ p188) ∨ (¬ p545) ∨ (¬ p796) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1159) ∨ (¬ p1256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p796 := by
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
  have u6 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13687 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18448 (p7 p123 p288 p304 p362 p434 p685 : Prop)
    (h16152 : (¬ p7))
    (h16186 : (¬ p123))
    (h3898 : p685)
    (h13688 : p7 ∨ p123 ∨ (¬ p288) ∨ (¬ p304) ∨ (¬ p362) ∨ (¬ p434) ∨ (¬ p685)) : (¬ p288) ∨ (¬ p304) ∨ (¬ p362) ∨ (¬ p434) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p288 := by
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
  have u3 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p123) := by
    exact h16186
  have u6 : p685 := by
    exact h3898
  rcases h13688 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step18449 (p7 p123 p279 p288 p304 p331 p362 p814 p858 p996 : Prop)
    (h16152 : (¬ p7))
    (h16186 : (¬ p123))
    (h1444 : p279)
    (h13689 : p7 ∨ p123 ∨ (¬ p279) ∨ (¬ p288) ∨ (¬ p304) ∨ (¬ p331) ∨ (¬ p362) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p996)) : (¬ p288) ∨ (¬ p304) ∨ (¬ p331) ∨ (¬ p362) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p331 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p362 := by
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
  have u6 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p123) := by
    exact h16186
  have u9 : p279 := by
    exact h1444
  rcases h13689 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)

theorem step18455 (p7 p156 p193 p728 p904 p923 p1330 p1349 p1489 : Prop)
    (h16152 : (¬ p7))
    (h13701 : p7 ∨ (¬ p156) ∨ (¬ p193) ∨ (¬ p728) ∨ (¬ p904) ∨ (¬ p923) ∨ (¬ p1330) ∨ (¬ p1349) ∨ (¬ p1489)) : (¬ p156) ∨ (¬ p193) ∨ (¬ p728) ∨ (¬ p904) ∨ (¬ p923) ∨ (¬ p1330) ∨ (¬ p1349) ∨ (¬ p1489) := by
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
  have u2 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p923 := by
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
  rcases h13701 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18456 (p7 p8 p42 p158 p193 p230 p728 p928 p1330 p1349 p1489 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16165 : (¬ p230))
    (h13702 : p7 ∨ (¬ p8) ∨ (¬ p42) ∨ (¬ p158) ∨ (¬ p193) ∨ p230 ∨ (¬ p728) ∨ (¬ p928) ∨ (¬ p1330) ∨ (¬ p1349) ∨ (¬ p1489)) : (¬ p8) ∨ (¬ p158) ∨ (¬ p193) ∨ (¬ p728) ∨ (¬ p928) ∨ (¬ p1330) ∨ (¬ p1349) ∨ (¬ p1489) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p928 := by
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
  have u9 : p42 := by
    exact h132
  have u10 : (¬ p230) := by
    exact h16165
  rcases h13702 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u10 q5)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step18457 (p7 p87 p101 p134 p189 p227 p262 p581 p1084 : Prop)
    (h16152 : (¬ p7))
    (h13703 : p7 ∨ (¬ p87) ∨ (¬ p101) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p227) ∨ (¬ p262) ∨ (¬ p581) ∨ (¬ p1084)) : (¬ p87) ∨ (¬ p101) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p227) ∨ (¬ p262) ∨ (¬ p581) ∨ (¬ p1084) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p101 := by
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
  have u4 : p227 := by
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
  have u7 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13703 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18458 (p7 p41 p101 p137 p189 p279 p576 p686 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16205 : (¬ p686))
    (h13704 : p7 ∨ (¬ p41) ∨ (¬ p101) ∨ (¬ p137) ∨ (¬ p189) ∨ (¬ p279) ∨ (¬ p576) ∨ p686) : (¬ p41) ∨ (¬ p101) ∨ (¬ p137) ∨ (¬ p189) ∨ (¬ p576) := by
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
  have u2 : p137 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p279 := by
    exact h1444
  have u7 : (¬ p686) := by
    exact h16205
  rcases h13704 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u4)
  · exact False.elim (u7 q7)

theorem step18459 (p7 p8 p21 p63 p101 p495 p657 p686 p924 p1098 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h8348 : p1386)
    (h13705 : p7 ∨ (¬ p8) ∨ (¬ p21) ∨ (¬ p63) ∨ (¬ p101) ∨ (¬ p495) ∨ (¬ p657) ∨ p686 ∨ (¬ p924) ∨ (¬ p1098) ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p8) ∨ (¬ p21) ∨ (¬ p63) ∨ (¬ p101) ∨ (¬ p495) ∨ (¬ p657) ∨ (¬ p924) ∨ (¬ p1098) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p21 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p101 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p686) := by
    exact h16205
  have u11 : p1386 := by
    exact h8348
  rcases h13705 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
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

theorem step18460 (p7 p8 p63 p161 p728 p924 p1098 p1232 p1330 : Prop)
    (h16152 : (¬ p7))
    (h13706 : p7 ∨ (¬ p8) ∨ (¬ p63) ∨ (¬ p161) ∨ (¬ p728) ∨ (¬ p924) ∨ (¬ p1098) ∨ (¬ p1232) ∨ (¬ p1330)) : (¬ p8) ∨ (¬ p63) ∨ (¬ p161) ∨ (¬ p728) ∨ (¬ p924) ∨ (¬ p1098) ∨ (¬ p1232) ∨ (¬ p1330) := by
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
  have u5 : p1098 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13706 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18461 (p7 p21 p63 p101 p495 p657 p680 p686 p687 p734 p924 p1098 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h6744 : p1135)
    (h13707 : p7 ∨ (¬ p21) ∨ (¬ p63) ∨ (¬ p101) ∨ (¬ p495) ∨ (¬ p657) ∨ (¬ p680) ∨ p686 ∨ (¬ p687) ∨ (¬ p734) ∨ (¬ p924) ∨ (¬ p1098) ∨ (¬ p1135)) : (¬ p21) ∨ (¬ p63) ∨ (¬ p101) ∨ (¬ p495) ∨ (¬ p657) ∨ (¬ p680) ∨ (¬ p687) ∨ (¬ p734) ∨ (¬ p924) ∨ (¬ p1098) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p21 := by
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
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p680 := by
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
  have u8 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1098 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  have u11 : (¬ p686) := by
    exact h16205
  have u12 : p1135 := by
    exact h6744
  rcases h13707 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
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

theorem step18462 (p7 p21 p101 p350 p495 p595 p596 : Prop)
    (h16152 : (¬ p7))
    (h13708 : p7 ∨ (¬ p21) ∨ (¬ p101) ∨ (¬ p350) ∨ (¬ p495) ∨ (¬ p595) ∨ (¬ p596)) : (¬ p21) ∨ (¬ p101) ∨ (¬ p350) ∨ (¬ p495) ∨ (¬ p595) ∨ (¬ p596) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p21 := by
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
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p596 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h13708 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step18463 (p7 p63 p161 p302 p616 p792 p1288 p1333 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h4535 : p792)
    (h13709 : p7 ∨ (¬ p63) ∨ (¬ p161) ∨ p302 ∨ (¬ p616) ∨ (¬ p792) ∨ (¬ p1288) ∨ (¬ p1333)) : (¬ p63) ∨ (¬ p161) ∨ (¬ p616) ∨ (¬ p1288) ∨ (¬ p1333) := by
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
  have u2 : p616 := by
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
  have u6 : (¬ p302) := by
    exact h16285
  have u7 : p792 := by
    exact h4535
  rcases h13709 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step18464 (p7 p18 p69 p101 p617 p657 p686 p687 p734 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h6744 : p1135)
    (h13710 : p7 ∨ (¬ p18) ∨ (¬ p69) ∨ (¬ p101) ∨ (¬ p617) ∨ (¬ p657) ∨ p686 ∨ (¬ p687) ∨ (¬ p734) ∨ (¬ p1135)) : (¬ p18) ∨ (¬ p69) ∨ (¬ p101) ∨ (¬ p617) ∨ (¬ p657) ∨ (¬ p687) ∨ (¬ p734) := by
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
  have u3 : p617 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p686) := by
    exact h16205
  have u9 : p1135 := by
    exact h6744
  rcases h13710 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18465 (p7 p15 p49 p84 p237 p351 p420 p495 p840 : Prop)
    (h16152 : (¬ p7))
    (h13711 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p237) ∨ (¬ p351) ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p840)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p237) ∨ (¬ p351) ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p840) := by
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
  have u4 : p351 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13711 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18466 (p21 p101 p577 p686 p792 : Prop)
    (h16205 : (¬ p686))
    (h4535 : p792)
    (h13712 : (¬ p21) ∨ (¬ p101) ∨ p577 ∨ p686 ∨ (¬ p792)) : (¬ p21) ∨ (¬ p101) ∨ p577 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p21 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p577) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : (¬ p686) := by
    exact h16205
  have u4 : p792 := by
    exact h4535
  rcases h13712 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u2 q2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)

theorem step18467 (p7 p8 p15 p21 p49 p101 p285 p495 p836 p927 p1098 : Prop)
    (h16152 : (¬ p7))
    (h13713 : p7 ∨ (¬ p8) ∨ (¬ p15) ∨ (¬ p21) ∨ (¬ p49) ∨ (¬ p101) ∨ (¬ p285) ∨ (¬ p495) ∨ (¬ p836) ∨ (¬ p927) ∨ (¬ p1098)) : (¬ p8) ∨ (¬ p15) ∨ (¬ p21) ∨ (¬ p49) ∨ (¬ p101) ∨ (¬ p285) ∨ (¬ p495) ∨ (¬ p836) ∨ (¬ p927) ∨ (¬ p1098) := by
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
  have u2 : p21 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p285 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p927 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1098 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h13713 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step18468 (p7 p18 p69 p86 p101 p126 p256 p350 : Prop)
    (h16152 : (¬ p7))
    (h13714 : p7 ∨ (¬ p18) ∨ (¬ p69) ∨ (¬ p86) ∨ (¬ p101) ∨ (¬ p126) ∨ (¬ p256) ∨ (¬ p350)) : (¬ p18) ∨ (¬ p69) ∨ (¬ p86) ∨ (¬ p101) ∨ (¬ p126) ∨ (¬ p256) ∨ (¬ p350) := by
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
  have u2 : p86 := by
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
  have u5 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13714 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18470 (p7 p101 p329 p350 p367 p690 p1366 : Prop)
    (h16152 : (¬ p7))
    (h13716 : p7 ∨ (¬ p101) ∨ (¬ p329) ∨ (¬ p350) ∨ (¬ p367) ∨ (¬ p690) ∨ (¬ p1366)) : (¬ p101) ∨ (¬ p329) ∨ (¬ p350) ∨ (¬ p367) ∨ (¬ p690) ∨ (¬ p1366) := by
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
  have u4 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h13716 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step18473 (p5 p6 p7 p10 p351 p595 p734 p1542 : Prop)
    (h16152 : (¬ p7))
    (h13719 : (¬ p5) ∨ (¬ p6) ∨ p7 ∨ (¬ p10) ∨ (¬ p351) ∨ (¬ p595) ∨ (¬ p734) ∨ (¬ p1542)) : (¬ p5) ∨ (¬ p6) ∨ (¬ p10) ∨ (¬ p351) ∨ (¬ p595) ∨ (¬ p734) ∨ (¬ p1542) := by
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
  have u3 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13719 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18474 (p7 p101 p329 p657 p686 p734 p1135 p1366 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h6744 : p1135)
    (h13720 : p7 ∨ (¬ p101) ∨ (¬ p329) ∨ (¬ p657) ∨ p686 ∨ (¬ p734) ∨ (¬ p1135) ∨ (¬ p1366)) : (¬ p101) ∨ (¬ p329) ∨ (¬ p657) ∨ (¬ p734) ∨ (¬ p1366) := by
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
  have u2 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p686) := by
    exact h16205
  have u7 : p1135 := by
    exact h6744
  rcases h13720 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step18475 (p5 p6 p7 p101 p455 p594 p620 p687 p1084 p1545 : Prop)
    (h16152 : (¬ p7))
    (h13722 : (¬ p5) ∨ (¬ p6) ∨ p7 ∨ (¬ p101) ∨ (¬ p455) ∨ (¬ p594) ∨ (¬ p620) ∨ (¬ p687) ∨ (¬ p1084) ∨ (¬ p1545)) : (¬ p5) ∨ (¬ p6) ∨ (¬ p101) ∨ (¬ p455) ∨ (¬ p594) ∨ (¬ p620) ∨ (¬ p687) ∨ (¬ p1084) ∨ (¬ p1545) := by
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
  have u3 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p594 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p620 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h13722 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u9 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step18476 (p7 p41 p42 p101 p207 p227 p456 p575 p686 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16205 : (¬ p686))
    (h13723 : p7 ∨ (¬ p41) ∨ (¬ p42) ∨ (¬ p101) ∨ (¬ p207) ∨ (¬ p227) ∨ (¬ p456) ∨ (¬ p575) ∨ p686) : (¬ p41) ∨ (¬ p101) ∨ (¬ p207) ∨ (¬ p227) ∨ (¬ p456) ∨ (¬ p575) := by
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
  have u2 : p207 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : p42 := by
    exact h132
  have u8 : (¬ p686) := by
    exact h16205
  rcases h13723 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (u8 q8)

theorem step18477 (p7 p90 p237 p839 p1022 p1387 p1545 : Prop)
    (h16152 : (¬ p7))
    (h13725 : p7 ∨ (¬ p90) ∨ (¬ p237) ∨ (¬ p839) ∨ (¬ p1022) ∨ (¬ p1387) ∨ (¬ p1545)) : (¬ p90) ∨ (¬ p237) ∨ (¬ p839) ∨ (¬ p1022) ∨ (¬ p1387) ∨ (¬ p1545) := by
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
  have u2 : p839 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1022 := by
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
  rcases h13725 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step18478 (p7 p90 p687 p820 p1015 p1385 : Prop)
    (h16152 : (¬ p7))
    (h13726 : p7 ∨ (¬ p90) ∨ (¬ p687) ∨ (¬ p820) ∨ (¬ p1015) ∨ (¬ p1385)) : (¬ p90) ∨ (¬ p687) ∨ (¬ p820) ∨ (¬ p1015) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p90 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p820 := by
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
  rcases h13726 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18481 (p7 p227 p456 p498 p575 p924 p1099 : Prop)
    (h16152 : (¬ p7))
    (h13729 : p7 ∨ (¬ p227) ∨ (¬ p456) ∨ (¬ p498) ∨ (¬ p575) ∨ (¬ p924) ∨ (¬ p1099)) : (¬ p227) ∨ (¬ p456) ∨ (¬ p498) ∨ (¬ p575) ∨ (¬ p924) ∨ (¬ p1099) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p456 := by
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
  rcases h13729 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step18482 (p7 p16 p101 p134 p189 p657 p686 p904 p1096 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h6744 : p1135)
    (h13730 : p7 ∨ (¬ p16) ∨ (¬ p101) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p657) ∨ p686 ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1135)) : (¬ p16) ∨ (¬ p101) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p657) ∨ (¬ p904) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p101 := by
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
  have u8 : (¬ p686) := by
    exact h16205
  have u9 : p1135 := by
    exact h6744
  rcases h13730 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18483 (p7 p8 p9 p16 p101 p134 p189 p638 p897 : Prop)
    (h16152 : (¬ p7))
    (h13731 : p7 ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p16) ∨ (¬ p101) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p638) ∨ (¬ p897)) : (¬ p8) ∨ (¬ p9) ∨ (¬ p16) ∨ (¬ p101) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p638) ∨ (¬ p897) := by
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
  have u2 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p638 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13731 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18484 (p7 p304 p348 p362 p638 p897 : Prop)
    (h16152 : (¬ p7))
    (h13732 : p7 ∨ (¬ p304) ∨ (¬ p348) ∨ (¬ p362) ∨ (¬ p638) ∨ (¬ p897)) : (¬ p304) ∨ (¬ p348) ∨ (¬ p362) ∨ (¬ p638) ∨ (¬ p897) := by
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
  have u3 : p638 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13732 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18486 (p7 p63 p789 p1136 p1333 p1386 p1393 : Prop)
    (h16152 : (¬ p7))
    (h16259 : (¬ p1136))
    (h8348 : p1386)
    (h13736 : p7 ∨ (¬ p63) ∨ (¬ p789) ∨ p1136 ∨ (¬ p1333) ∨ (¬ p1386) ∨ (¬ p1393)) : (¬ p63) ∨ (¬ p789) ∨ (¬ p1333) ∨ (¬ p1393) := by
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
  have u2 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p1136) := by
    exact h16259
  have u6 : p1386 := by
    exact h8348
  rcases h13736 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step18487 (p7 p8 p244 p835 p928 p1385 : Prop)
    (h16152 : (¬ p7))
    (h13737 : p7 ∨ (¬ p8) ∨ (¬ p244) ∨ (¬ p835) ∨ (¬ p928) ∨ (¬ p1385)) : (¬ p8) ∨ (¬ p244) ∨ (¬ p835) ∨ (¬ p928) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p244 := by
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
  rcases h13737 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18489 (p7 p16 p189 p419 p665 p796 p1095 p1096 : Prop)
    (h16152 : (¬ p7))
    (h13740 : p7 ∨ (¬ p16) ∨ (¬ p189) ∨ (¬ p419) ∨ (¬ p665) ∨ (¬ p796) ∨ (¬ p1095) ∨ (¬ p1096)) : (¬ p16) ∨ (¬ p189) ∨ (¬ p419) ∨ (¬ p665) ∨ (¬ p796) ∨ (¬ p1095) ∨ (¬ p1096) := by
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
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p796 := by
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
  rcases h13740 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18490 (p2 p7 p101 p134 p424 p659 p686 : Prop)
    (h16152 : (¬ p7))
    (h3753 : p659)
    (h16205 : (¬ p686))
    (h13741 : (¬ p2) ∨ p7 ∨ (¬ p101) ∨ (¬ p134) ∨ (¬ p424) ∨ (¬ p659) ∨ p686) : (¬ p2) ∨ (¬ p101) ∨ (¬ p134) ∨ (¬ p424) := by
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
  have u5 : p659 := by
    exact h3753
  have u6 : (¬ p686) := by
    exact h16205
  rcases h13741 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)

theorem step18491 (p7 p23 p303 p329 p420 p996 : Prop)
    (h16152 : (¬ p7))
    (h13742 : p7 ∨ (¬ p23) ∨ (¬ p303) ∨ (¬ p329) ∨ (¬ p420) ∨ (¬ p996)) : (¬ p23) ∨ (¬ p303) ∨ (¬ p329) ∨ (¬ p420) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p23 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p329 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13742 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18492 (p7 p17 p45 p101 p137 p193 p686 p792 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h4535 : p792)
    (h13744 : p7 ∨ (¬ p17) ∨ (¬ p45) ∨ (¬ p101) ∨ (¬ p137) ∨ (¬ p193) ∨ p686 ∨ (¬ p792)) : (¬ p17) ∨ (¬ p45) ∨ (¬ p101) ∨ (¬ p137) ∨ (¬ p193) := by
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
  have u2 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p137 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p686) := by
    exact h16205
  have u7 : p792 := by
    exact h4535
  rcases h13744 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u6 q6)
  · exact False.elim (q7 u7)

theorem step18493 (p7 p285 p304 p348 p362 p836 : Prop)
    (h16152 : (¬ p7))
    (h13745 : p7 ∨ (¬ p285) ∨ (¬ p304) ∨ (¬ p348) ∨ (¬ p362) ∨ (¬ p836)) : (¬ p285) ∨ (¬ p304) ∨ (¬ p348) ∨ (¬ p362) ∨ (¬ p836) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p285 := by
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
  have u4 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13745 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18494 (p2 p5 p7 p63 p343 p419 p840 p928 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16309 : (¬ p1324))
    (h13747 : (¬ p2) ∨ (¬ p5) ∨ p7 ∨ (¬ p63) ∨ (¬ p343) ∨ (¬ p419) ∨ (¬ p840) ∨ (¬ p928) ∨ p1324 ∨ (¬ p1325)) : (¬ p2) ∨ (¬ p5) ∨ (¬ p63) ∨ (¬ p419) ∨ (¬ p840) ∨ (¬ p928) ∨ (¬ p1325) := by
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
  have u3 : p419 := by
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
  rcases h13747 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18496 (p2 p5 p7 p89 p237 p419 p876 p918 p1324 p1325 p1393 : Prop)
    (h16152 : (¬ p7))
    (h5054 : p876)
    (h16309 : (¬ p1324))
    (h13749 : (¬ p2) ∨ (¬ p5) ∨ p7 ∨ (¬ p89) ∨ (¬ p237) ∨ (¬ p419) ∨ (¬ p876) ∨ (¬ p918) ∨ p1324 ∨ (¬ p1325) ∨ (¬ p1393)) : (¬ p2) ∨ (¬ p5) ∨ (¬ p89) ∨ (¬ p237) ∨ (¬ p419) ∨ (¬ p918) ∨ (¬ p1325) ∨ (¬ p1393) := by
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
  have u2 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p876 := by
    exact h5054
  have u10 : (¬ p1324) := by
    exact h16309
  rcases h13749 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u8 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u5)
  · exact False.elim (u10 q8)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step18498 (p7 p304 p343 p362 p434 p686 p734 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16205 : (¬ p686))
    (h13751 : p7 ∨ (¬ p304) ∨ (¬ p343) ∨ (¬ p362) ∨ (¬ p434) ∨ p686 ∨ (¬ p734)) : (¬ p304) ∨ (¬ p362) ∨ (¬ p434) ∨ (¬ p734) := by
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
  rcases h13751 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step18499 (p7 p63 p685 p728 p840 p928 p1136 : Prop)
    (h16152 : (¬ p7))
    (h3898 : p685)
    (h16259 : (¬ p1136))
    (h13752 : p7 ∨ (¬ p63) ∨ (¬ p685) ∨ (¬ p728) ∨ (¬ p840) ∨ (¬ p928) ∨ p1136) : (¬ p63) ∨ (¬ p728) ∨ (¬ p840) ∨ (¬ p928) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p728 := by
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
  have u5 : p685 := by
    exact h3898
  have u6 : (¬ p1136) := by
    exact h16259
  rcases h13752 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step18501 (p7 p63 p102 p257 p495 p636 p792 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h4535 : p792)
    (h13754 : p7 ∨ (¬ p63) ∨ (¬ p102) ∨ p257 ∨ (¬ p495) ∨ (¬ p636) ∨ (¬ p792)) : (¬ p63) ∨ (¬ p102) ∨ (¬ p495) ∨ (¬ p636) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p102 := by
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
  have u5 : (¬ p257) := by
    exact h16170
  have u6 : p792 := by
    exact h4535
  rcases h13754 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step18502 (p7 p102 p227 p257 p304 p1386 p1452 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h8348 : p1386)
    (h13755 : p7 ∨ (¬ p102) ∨ (¬ p227) ∨ p257 ∨ (¬ p304) ∨ (¬ p1386) ∨ (¬ p1452)) : (¬ p102) ∨ (¬ p227) ∨ (¬ p304) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p102 := by
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
  have u3 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p257) := by
    exact h16170
  have u6 : p1386 := by
    exact h8348
  rcases h13755 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step18503 (p7 p45 p85 p422 p1184 p1324 p1465 : Prop)
    (h16152 : (¬ p7))
    (h7053 : p1184)
    (h16309 : (¬ p1324))
    (h13756 : p7 ∨ (¬ p45) ∨ (¬ p85) ∨ (¬ p422) ∨ (¬ p1184) ∨ p1324 ∨ (¬ p1465)) : (¬ p45) ∨ (¬ p85) ∨ (¬ p422) ∨ (¬ p1465) := by
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
  have u3 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p1184 := by
    exact h7053
  have u6 : (¬ p1324) := by
    exact h16309
  rcases h13756 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step18504 (p7 p69 p796 p875 p1141 p1184 p1256 : Prop)
    (h16152 : (¬ p7))
    (h16220 : (¬ p875))
    (h7053 : p1184)
    (h13757 : p7 ∨ (¬ p69) ∨ (¬ p796) ∨ p875 ∨ (¬ p1141) ∨ (¬ p1184) ∨ (¬ p1256)) : (¬ p69) ∨ (¬ p796) ∨ (¬ p1141) ∨ (¬ p1256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p796 := by
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
  have u5 : (¬ p875) := by
    exact h16220
  have u6 : p1184 := by
    exact h7053
  rcases h13757 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step18505 (p7 p8 p85 p102 p257 p306 p728 p1184 p1249 p1330 p1489 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h7053 : p1184)
    (h13758 : p7 ∨ (¬ p8) ∨ (¬ p85) ∨ (¬ p102) ∨ p257 ∨ (¬ p306) ∨ (¬ p728) ∨ (¬ p1184) ∨ (¬ p1249) ∨ (¬ p1330) ∨ (¬ p1489)) : (¬ p8) ∨ (¬ p85) ∨ (¬ p102) ∨ (¬ p306) ∨ (¬ p728) ∨ (¬ p1249) ∨ (¬ p1330) ∨ (¬ p1489) := by
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
  have u2 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p306 := by
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
  have u9 : (¬ p257) := by
    exact h16170
  have u10 : p1184 := by
    exact h7053
  rcases h13758 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step18506 (p7 p45 p85 p102 p257 p304 p331 p362 p796 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h7053 : p1184)
    (h13759 : p7 ∨ (¬ p45) ∨ (¬ p85) ∨ (¬ p102) ∨ p257 ∨ (¬ p304) ∨ (¬ p331) ∨ (¬ p362) ∨ (¬ p796) ∨ (¬ p1184)) : (¬ p45) ∨ (¬ p85) ∨ (¬ p102) ∨ (¬ p304) ∨ (¬ p331) ∨ (¬ p362) ∨ (¬ p796) := by
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
  have u2 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p331 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p257) := by
    exact h16170
  have u9 : p1184 := by
    exact h7053
  rcases h13759 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18507 (p7 p102 p257 p304 p362 p387 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h6744 : p1135)
    (h13760 : p7 ∨ (¬ p102) ∨ p257 ∨ (¬ p304) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p1135)) : (¬ p102) ∨ (¬ p304) ∨ (¬ p362) ∨ (¬ p387) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p102 := by
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
  have u5 : (¬ p257) := by
    exact h16170
  have u6 : p1135 := by
    exact h6744
  rcases h13760 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step18508 (p7 p15 p22 p125 p494 p601 : Prop)
    (h16152 : (¬ p7))
    (h13762 : p7 ∨ (¬ p15) ∨ (¬ p22) ∨ (¬ p125) ∨ (¬ p494) ∨ (¬ p601)) : (¬ p15) ∨ (¬ p22) ∨ (¬ p125) ∨ (¬ p494) ∨ (¬ p601) := by
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
  have u2 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13762 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18509 (p7 p122 p160 p236 p304 p532 p633 p1160 : Prop)
    (h16152 : (¬ p7))
    (h10260 : p122)
    (h16265 : (¬ p1160))
    (h13765 : p7 ∨ (¬ p122) ∨ (¬ p160) ∨ (¬ p236) ∨ (¬ p304) ∨ (¬ p532) ∨ (¬ p633) ∨ p1160) : (¬ p160) ∨ (¬ p236) ∨ (¬ p304) ∨ (¬ p532) ∨ (¬ p633) := by
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
  have u2 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p122 := by
    exact h10260
  have u7 : (¬ p1160) := by
    exact h16265
  rcases h13765 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u7 q7)

theorem step18510 (p7 p161 p227 p304 p633 p1035 p1160 p1184 p1214 p1232 : Prop)
    (h16152 : (¬ p7))
    (h16265 : (¬ p1160))
    (h7053 : p1184)
    (h13766 : p7 ∨ (¬ p161) ∨ (¬ p227) ∨ (¬ p304) ∨ (¬ p633) ∨ (¬ p1035) ∨ p1160 ∨ (¬ p1184) ∨ (¬ p1214) ∨ (¬ p1232)) : (¬ p161) ∨ (¬ p227) ∨ (¬ p304) ∨ (¬ p633) ∨ (¬ p1035) ∨ (¬ p1214) ∨ (¬ p1232) := by
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
  have u3 : p633 := by
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
  have u6 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p1160) := by
    exact h16265
  have u9 : p1184 := by
    exact h7053
  rcases h13766 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u8 q6)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)

theorem step18511 (p7 p102 p257 p279 p304 p331 p362 p814 p858 p996 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h1444 : p279)
    (h13767 : p7 ∨ (¬ p102) ∨ p257 ∨ (¬ p279) ∨ (¬ p304) ∨ (¬ p331) ∨ (¬ p362) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p996)) : (¬ p102) ∨ (¬ p304) ∨ (¬ p331) ∨ (¬ p362) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p331 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p362 := by
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
  have u6 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p257) := by
    exact h16170
  have u9 : p279 := by
    exact h1444
  rcases h13767 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18512 (p7 p382 p818 p861 p1273 p1385 : Prop)
    (h16152 : (¬ p7))
    (h13768 : p7 ∨ (¬ p382) ∨ (¬ p818) ∨ (¬ p861) ∨ (¬ p1273) ∨ (¬ p1385)) : (¬ p382) ∨ (¬ p818) ∨ (¬ p861) ∨ (¬ p1273) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p818 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p861 := by
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
  rcases h13768 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18513 (p7 p162 p382 p789 p918 p1393 p1709 : Prop)
    (h16152 : (¬ p7))
    (h16160 : (¬ p162))
    (h10799 : p1709)
    (h13769 : p7 ∨ p162 ∨ (¬ p382) ∨ (¬ p789) ∨ (¬ p918) ∨ (¬ p1393) ∨ (¬ p1709)) : (¬ p382) ∨ (¬ p789) ∨ (¬ p918) ∨ (¬ p1393) := by
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
  have u5 : (¬ p162) := by
    exact h16160
  have u6 : p1709 := by
    exact h10799
  rcases h13769 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step18514 (p7 p102 p257 p258 p343 p519 p734 p1022 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h1950 : p343)
    (h13770 : p7 ∨ (¬ p102) ∨ p257 ∨ (¬ p258) ∨ (¬ p343) ∨ (¬ p519) ∨ (¬ p734) ∨ (¬ p1022)) : (¬ p102) ∨ (¬ p258) ∨ (¬ p519) ∨ (¬ p734) ∨ (¬ p1022) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p102 := by
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
  have u4 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p257) := by
    exact h16170
  have u7 : p343 := by
    exact h1950
  rcases h13770 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step18515 (p7 p102 p257 p304 p348 p362 p685 p728 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h3898 : p685)
    (h13771 : p7 ∨ (¬ p102) ∨ p257 ∨ (¬ p304) ∨ (¬ p348) ∨ (¬ p362) ∨ (¬ p685) ∨ (¬ p728)) : (¬ p102) ∨ (¬ p304) ∨ (¬ p348) ∨ (¬ p362) ∨ (¬ p728) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p102 := by
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
  have u4 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p257) := by
    exact h16170
  have u7 : p685 := by
    exact h3898
  rcases h13771 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step18517 (p7 p69 p86 p237 p533 p537 p1141 p1465 : Prop)
    (h16152 : (¬ p7))
    (h13773 : p7 ∨ (¬ p69) ∨ (¬ p86) ∨ (¬ p237) ∨ (¬ p533) ∨ (¬ p537) ∨ (¬ p1141) ∨ (¬ p1465)) : (¬ p69) ∨ (¬ p86) ∨ (¬ p237) ∨ (¬ p533) ∨ (¬ p537) ∨ (¬ p1141) ∨ (¬ p1465) := by
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
  have u3 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13773 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18518 (p7 p63 p126 p331 p382 p581 p621 p996 : Prop)
    (h16152 : (¬ p7))
    (h13774 : p7 ∨ (¬ p63) ∨ (¬ p126) ∨ (¬ p331) ∨ (¬ p382) ∨ (¬ p581) ∨ (¬ p621) ∨ (¬ p996)) : (¬ p63) ∨ (¬ p126) ∨ (¬ p331) ∨ (¬ p382) ∨ (¬ p581) ∨ (¬ p621) ∨ (¬ p996) := by
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
  have u2 : p331 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p621 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13774 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18520 (p7 p102 p257 p387 p601 p636 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h6744 : p1135)
    (h13776 : p7 ∨ (¬ p102) ∨ p257 ∨ (¬ p387) ∨ (¬ p601) ∨ (¬ p636) ∨ (¬ p1135)) : (¬ p102) ∨ (¬ p387) ∨ (¬ p601) ∨ (¬ p636) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p387 := by
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
  have u5 : (¬ p257) := by
    exact h16170
  have u6 : p1135 := by
    exact h6744
  rcases h13776 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step18521 (p7 p8 p102 p257 p306 p836 p1116 p1139 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h6761 : p1139)
    (h13777 : p7 ∨ (¬ p8) ∨ (¬ p102) ∨ p257 ∨ (¬ p306) ∨ (¬ p836) ∨ (¬ p1116) ∨ (¬ p1139)) : (¬ p8) ∨ (¬ p102) ∨ (¬ p306) ∨ (¬ p836) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
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
  have u6 : (¬ p257) := by
    exact h16170
  have u7 : p1139 := by
    exact h6761
  rcases h13777 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step18523 (p7 p22 p227 p228 p304 p419 p633 p1187 : Prop)
    (h16152 : (¬ p7))
    (h13780 : p7 ∨ (¬ p22) ∨ (¬ p227) ∨ (¬ p228) ∨ (¬ p304) ∨ (¬ p419) ∨ (¬ p633) ∨ (¬ p1187)) : (¬ p22) ∨ (¬ p227) ∨ (¬ p228) ∨ (¬ p304) ∨ (¬ p419) ∨ (¬ p633) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p22 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13780 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step18524 (p7 p258 p576 p686 p788 p1206 p1273 p1495 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h5066 : p788)
    (h13782 : p7 ∨ (¬ p258) ∨ (¬ p576) ∨ p686 ∨ (¬ p788) ∨ (¬ p1206) ∨ (¬ p1273) ∨ (¬ p1495)) : (¬ p258) ∨ (¬ p576) ∨ (¬ p1206) ∨ (¬ p1273) ∨ (¬ p1495) := by
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
  have u6 : (¬ p686) := by
    exact h16205
  have u7 : p788 := by
    exact h5066
  rcases h13782 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step18525 (p2 p7 p45 p192 p419 p426 p657 p792 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h4535 : p792)
    (h13783 : (¬ p2) ∨ p7 ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p419) ∨ p426 ∨ (¬ p657) ∨ (¬ p792)) : (¬ p2) ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p419) ∨ (¬ p657) := by
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
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p426) := by
    exact h16178
  have u7 : p792 := by
    exact h4535
  rcases h13783 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step18526 (p2 p3 p7 p109 p288 p301 p302 p323 p419 p1075 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h6478 : p1075)
    (h13785 : (¬ p2) ∨ (¬ p3) ∨ p7 ∨ (¬ p109) ∨ (¬ p288) ∨ (¬ p301) ∨ p302 ∨ (¬ p323) ∨ (¬ p419) ∨ (¬ p1075)) : (¬ p2) ∨ (¬ p3) ∨ (¬ p109) ∨ (¬ p288) ∨ (¬ p301) ∨ (¬ p323) ∨ (¬ p419) := by
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
  have u2 : p109 := by
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
  have u5 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p302) := by
    exact h16285
  have u9 : p1075 := by
    exact h6478
  rcases h13785 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u8 q6)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u9)

theorem step18527 (p2 p7 p45 p192 p302 p419 p928 p1537 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h9400 : p1537)
    (h13786 : (¬ p2) ∨ p7 ∨ (¬ p45) ∨ (¬ p192) ∨ p302 ∨ (¬ p419) ∨ (¬ p928) ∨ (¬ p1537)) : (¬ p2) ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p419) ∨ (¬ p928) := by
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
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p302) := by
    exact h16285
  have u7 : p1537 := by
    exact h9400
  rcases h13786 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step18528 (p7 p45 p90 p126 p192 p225 p226 p256 p347 : Prop)
    (h16152 : (¬ p7))
    (h13787 : p7 ∨ (¬ p45) ∨ (¬ p90) ∨ (¬ p126) ∨ (¬ p192) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p256) ∨ (¬ p347)) : (¬ p45) ∨ (¬ p90) ∨ (¬ p126) ∨ (¬ p192) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p256) ∨ (¬ p347) := by
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
  have u2 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p192 := by
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
  have u6 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h13787 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step18529 (p121 p257 p1075 p1080 : Prop)
    (h16170 : (¬ p257))
    (h6478 : p1075)
    (h13788 : (¬ p121) ∨ p257 ∨ (¬ p1075) ∨ p1080) : (¬ p121) ∨ p1080 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1080) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p257) := by
    exact h16170
  have u3 : p1075 := by
    exact h6478
  rcases h13788 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (u1 q3)

theorem step18530 (p7 p45 p90 p110 p192 p256 p288 p544 p556 p710 : Prop)
    (h16152 : (¬ p7))
    (h13789 : p7 ∨ (¬ p45) ∨ (¬ p90) ∨ (¬ p110) ∨ (¬ p192) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p544) ∨ (¬ p556) ∨ (¬ p710)) : (¬ p45) ∨ (¬ p90) ∨ (¬ p110) ∨ (¬ p192) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p544) ∨ (¬ p556) ∨ (¬ p710) := by
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
  have u2 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p192 := by
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
  have u6 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p556 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h13789 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step18531 (p2 p3 p7 p128 p229 p302 p419 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16285 : (¬ p302))
    (h13791 : (¬ p2) ∨ (¬ p3) ∨ p7 ∨ (¬ p128) ∨ (¬ p229) ∨ p302 ∨ (¬ p419)) : (¬ p2) ∨ (¬ p3) ∨ (¬ p229) ∨ (¬ p419) := by
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
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p128 := by
    exact h653
  have u6 : (¬ p302) := by
    exact h16285
  rcases h13791 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u4 q2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step18532 (p7 p43 p90 p163 p193 p229 : Prop)
    (h16152 : (¬ p7))
    (h13792 : p7 ∨ (¬ p43) ∨ (¬ p90) ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p229)) : (¬ p43) ∨ (¬ p90) ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p90 := by
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
  have u4 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13792 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18533 (p7 p45 p192 p224 p225 p226 p302 p792 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h4535 : p792)
    (h13795 : p7 ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p226) ∨ p302 ∨ (¬ p792)) : (¬ p45) ∨ (¬ p192) ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p226) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p302) := by
    exact h16285
  have u7 : p792 := by
    exact h4535
  rcases h13795 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u6 q6)
  · exact False.elim (q7 u7)

theorem step18534 (p2 p7 p211 p227 p228 p419 : Prop)
    (h16152 : (¬ p7))
    (h13797 : (¬ p2) ∨ p7 ∨ (¬ p211) ∨ (¬ p227) ∨ (¬ p228) ∨ (¬ p419)) : (¬ p2) ∨ (¬ p211) ∨ (¬ p227) ∨ (¬ p228) ∨ (¬ p419) := by
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
  have u3 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13797 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step18535 (p7 p189 p279 p419 p426 p657 p796 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16178 : (¬ p426))
    (h13798 : p7 ∨ (¬ p189) ∨ (¬ p279) ∨ (¬ p419) ∨ p426 ∨ (¬ p657) ∨ (¬ p796)) : (¬ p189) ∨ (¬ p419) ∨ (¬ p657) ∨ (¬ p796) := by
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
  have u5 : p279 := by
    exact h1444
  have u6 : (¬ p426) := by
    exact h16178
  rcases h13798 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

#print axioms step18535

end NineRUPTrial
