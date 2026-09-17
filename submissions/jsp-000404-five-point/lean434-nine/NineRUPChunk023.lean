import Mathlib.Tactic.Tauto

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

namespace NineRUPTrial

theorem step31602 (p63 p85 p382 p406 p620 p1287 p1394 : Prop)
    (h26869 : p406 ∨ p382)
    (h26835 : p85 ∨ p63)
    (h16565 : (¬ p85) ∨ (¬ p406) ∨ (¬ p620) ∨ (¬ p1287) ∨ (¬ p1394)) : p382 ∨ (¬ p620) ∨ (¬ p1287) ∨ (¬ p1394) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p620 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1394 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16565 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)

theorem step31603 (p15 p47 p63 p85 p156 p918 : Prop)
    (h26835 : p85 ∨ p63)
    (h16437 : (¬ p15) ∨ (¬ p47) ∨ (¬ p85) ∨ (¬ p156) ∨ (¬ p918)) : (¬ p15) ∨ p63 ∨ (¬ p47) ∨ (¬ p156) ∨ (¬ p918) := by
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
  have u3 : p156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16437 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)

theorem step31604 (p6 p10 p63 p85 p127 p258 p303 p323 p387 p576 : Prop)
    (h26839 : p127 ∨ p6)
    (h26861 : p323 ∨ p10)
    (h26867 : p387 ∨ p303)
    (h26835 : p85 ∨ p63)
    (h26128 : (¬ p576) ∨ (¬ p258) ∨ (¬ p127) ∨ (¬ p85) ∨ (¬ p387) ∨ (¬ p323)) : (¬ p258) ∨ p6 ∨ (¬ p576) ∨ p10 ∨ p303 ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26128 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u7)

theorem step31605 (p10 p15 p18 p19 p63 p85 p323 : Prop)
    (h26829 : p19 ∨ p18)
    (h26835 : p85 ∨ p63)
    (h26861 : p323 ∨ p10)
    (h16532 : (¬ p15) ∨ (¬ p19) ∨ (¬ p85) ∨ (¬ p323)) : (¬ p15) ∨ p18 ∨ p63 ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p18) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16532 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)

theorem step31607 (p90 p185 p237 p836 p840 p897 p918 : Prop)
    (h26851 : p237 ∨ p185)
    (h26895 : p840 ∨ p836)
    (h26586 : p90)
    (h21468 : (¬ p897) ∨ p918 ∨ (¬ p90) ∨ (¬ p840) ∨ (¬ p237)) : p185 ∨ (¬ p897) ∨ p918 ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p185) := fun hu => hn (Or.inl hu)
  have u1 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p90 := by
    exact h26586
  rcases h21468 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)

theorem step31609 (p63 p347 p368 p421 p438 p577 p687 p897 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h18174 : (¬ p63) ∨ (¬ p347) ∨ (¬ p368) ∨ (¬ p421) ∨ (¬ p438) ∨ (¬ p577) ∨ (¬ p687) ∨ (¬ p897) ∨ (¬ p1099)) : (¬ p687) ∨ (¬ p421) ∨ (¬ p63) ∨ p1096 ∨ (¬ p347) ∨ (¬ p438) ∨ (¬ p897) ∨ (¬ p368) ∨ (¬ p577) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18174 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u9)

theorem step31611 (p63 p125 p161 p362 p421 p434 p577 p1229 p1232 p1330 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h26865 : p362 ∨ p125)
    (h18162 : (¬ p63) ∨ (¬ p161) ∨ (¬ p362) ∨ (¬ p421) ∨ (¬ p434) ∨ (¬ p577) ∨ (¬ p1232) ∨ (¬ p1330)) : (¬ p434) ∨ p1229 ∨ p125 ∨ (¬ p1330) ∨ (¬ p161) ∨ (¬ p577) ∨ (¬ p63) ∨ (¬ p421) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18162 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u3)

theorem step31616 (p17 p185 p237 p344 p346 p836 p840 : Prop)
    (h26851 : p237 ∨ p185)
    (h26863 : p346 ∨ p344)
    (h26895 : p840 ∨ p836)
    (h17131 : (¬ p17) ∨ (¬ p237) ∨ (¬ p346) ∨ (¬ p840)) : p185 ∨ (¬ p17) ∨ p344 ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p185) := fun hu => hn (Or.inl hu)
  have u1 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17131 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)

theorem step31618 (p17 p185 p237 p1076 p1115 p1116 : Prop)
    (h26851 : p237 ∨ p185)
    (h26915 : p1116 ∨ p1115)
    (h17232 : (¬ p17) ∨ (¬ p237) ∨ (¬ p1076) ∨ (¬ p1116)) : p185 ∨ (¬ p1076) ∨ p1115 ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p185) := fun hu => hn (Or.inl hu)
  have u1 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
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
  rcases h17232 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)

theorem step31620 (p17 p185 p224 p237 p657 p836 p840 : Prop)
    (h26851 : p237 ∨ p185)
    (h26895 : p840 ∨ p836)
    (h26887 : p657 ∨ p224)
    (h17483 : (¬ p17) ∨ (¬ p237) ∨ (¬ p657) ∨ (¬ p840)) : p185 ∨ (¬ p17) ∨ p836 ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p185) := fun hu => hn (Or.inl hu)
  have u1 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17483 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)

theorem step31622 (p17 p303 p345 p382 p406 p576 p581 p820 : Prop)
    (h26869 : p406 ∨ p382)
    (h26879 : p581 ∨ p576)
    (h19765 : (¬ p17) ∨ (¬ p303) ∨ (¬ p345) ∨ (¬ p406) ∨ (¬ p581) ∨ (¬ p820)) : p382 ∨ (¬ p820) ∨ (¬ p303) ∨ p576 ∨ (¬ p345) ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p820 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p345 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19765 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u1)

theorem step31623 (p17 p224 p258 p344 p346 : Prop)
    (h26863 : p346 ∨ p344)
    (h20100 : (¬ p17) ∨ (¬ p224) ∨ (¬ p258) ∨ (¬ p346)) : (¬ p258) ∨ p344 ∨ (¬ p224) ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20100 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)

theorem step31624 (p17 p189 p193 p258 p1076 : Prop)
    (h26845 : p193 ∨ p189)
    (h17587 : (¬ p17) ∨ (¬ p193) ∨ (¬ p258) ∨ (¬ p1076)) : (¬ p17) ∨ (¬ p258) ∨ p189 ∨ (¬ p1076) := by
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
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17587 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)

theorem step31625 (p17 p101 p102 p189 p193 p258 : Prop)
    (h26837 : p102 ∨ p101)
    (h26845 : p193 ∨ p189)
    (h21007 : (¬ p17) ∨ (¬ p102) ∨ (¬ p193) ∨ (¬ p258)) : (¬ p258) ∨ p101 ∨ p189 ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p101) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h21007 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)

theorem step31626 (p15 p17 p39 p69 p88 p1035 p1145 p1229 p1454 p1644 : Prop)
    (h26833 : p69 ∨ p15)
    (h19145 : (¬ p17) ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p1035) ∨ (¬ p1145) ∨ (¬ p1229) ∨ (¬ p1454) ∨ (¬ p1644)) : (¬ p1454) ∨ (¬ p1644) ∨ (¬ p88) ∨ p15 ∨ (¬ p1035) ∨ (¬ p1145) ∨ (¬ p1229) ∨ (¬ p39) ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1454 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1644 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
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
  have u7 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19145 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u0)
  · exact False.elim (q8 u1)

theorem step31627 (p17 p109 p137 p163 p189 p193 : Prop)
    (h26845 : p193 ∨ p189)
    (h17923 : (¬ p17) ∨ (¬ p109) ∨ (¬ p137) ∨ (¬ p163) ∨ (¬ p193)) : p189 ∨ (¬ p17) ∨ (¬ p109) ∨ (¬ p137) ∨ (¬ p163) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p189) := fun hu => hn (Or.inl hu)
  have u1 : p17 := by
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
  have u4 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17923 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)

theorem step31628 (p3 p17 p41 p45 p83 p224 p225 p544 p576 p581 p657 : Prop)
    (h26877 : p544 ∨ p225)
    (h26879 : p581 ∨ p576)
    (h26887 : p657 ∨ p224)
    (h26831 : p45 ∨ p41)
    (h26130 : (¬ p83) ∨ (¬ p45) ∨ (¬ p657) ∨ (¬ p3) ∨ (¬ p17) ∨ (¬ p544) ∨ (¬ p581)) : (¬ p3) ∨ p225 ∨ p576 ∨ p224 ∨ (¬ p83) ∨ (¬ p17) ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h26130 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u8)

theorem step31629 (p3 p14 p16 p17 p71 p126 p229 p234 p301 p327 : Prop)
    (h26849 : p229 ∨ p14)
    (h26857 : p301 ∨ p126)
    (h17711 : (¬ p3) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p71) ∨ (¬ p229) ∨ (¬ p234) ∨ (¬ p301) ∨ (¬ p327)) : p14 ∨ (¬ p3) ∨ (¬ p17) ∨ (¬ p16) ∨ (¬ p234) ∨ (¬ p327) ∨ p126 ∨ (¬ p71) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p327 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p126) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h17711 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u5)

theorem step31631 (p2 p16 p17 p71 p126 p224 p301 p348 p481 p1189 p1542 : Prop)
    (h26873 : p481 ∨ p2)
    (h26857 : p301 ∨ p126)
    (h26131 : (¬ p1189) ∨ p348 ∨ (¬ p17) ∨ (¬ p16) ∨ (¬ p71) ∨ (¬ p481) ∨ (¬ p301) ∨ (¬ p1542) ∨ (¬ p224)) : (¬ p1189) ∨ p348 ∨ (¬ p17) ∨ (¬ p16) ∨ (¬ p71) ∨ p2 ∨ p126 ∨ (¬ p1542) ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p348) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p126) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h26131 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u8)

theorem step31632 (p6 p16 p17 p18 p71 p127 p234 p258 p328 p350 : Prop)
    (h26839 : p127 ∨ p6)
    (h19193 : (¬ p16) ∨ (¬ p17) ∨ (¬ p18) ∨ (¬ p71) ∨ (¬ p127) ∨ (¬ p234) ∨ (¬ p258) ∨ (¬ p328) ∨ (¬ p350)) : (¬ p71) ∨ (¬ p234) ∨ (¬ p17) ∨ (¬ p350) ∨ p6 ∨ (¬ p16) ∨ (¬ p258) ∨ (¬ p328) ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p16 := by
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
  have u8 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19193 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u3)

theorem step31633 (p15 p49 p125 p420 p494 p580 p601 : Prop)
    (h26881 : p601 ∨ p420)
    (h16473 : (¬ p15) ∨ (¬ p49) ∨ (¬ p125) ∨ (¬ p494) ∨ (¬ p580) ∨ (¬ p601)) : (¬ p15) ∨ (¬ p125) ∨ (¬ p494) ∨ p420 ∨ (¬ p580) ∨ (¬ p49) := by
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
  have u2 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p580 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16473 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)

theorem step31635 (p125 p265 p284 p420 p580 p601 p918 : Prop)
    (h26881 : p601 ∨ p420)
    (h18784 : (¬ p125) ∨ (¬ p265) ∨ (¬ p284) ∨ (¬ p580) ∨ (¬ p601) ∨ (¬ p918)) : (¬ p284) ∨ (¬ p918) ∨ p420 ∨ (¬ p265) ∨ (¬ p580) ∨ (¬ p125) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p284 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p580 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18784 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)

theorem step31637 (p6 p420 p455 p456 p601 p1140 p1211 : Prop)
    (h26871 : p456 ∨ p455)
    (h26881 : p601 ∨ p420)
    (h18066 : (¬ p6) ∨ (¬ p456) ∨ (¬ p601) ∨ (¬ p1140) ∨ (¬ p1211)) : p455 ∨ (¬ p1140) ∨ (¬ p1211) ∨ (¬ p6) ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18066 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)

theorem step31638 (p10 p21 p420 p601 : Prop)
    (h26881 : p601 ∨ p420)
    (h13396 : (¬ p10) ∨ (¬ p21) ∨ (¬ p601)) : (¬ p10) ∨ p420 ∨ (¬ p21) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p420) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p21 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h13396 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)

theorem step31639 (p10 p25 p50 p134 p420 p601 : Prop)
    (h26881 : p601 ∨ p420)
    (h17117 : (¬ p10) ∨ (¬ p25) ∨ (¬ p50) ∨ (¬ p134) ∨ (¬ p601)) : (¬ p10) ∨ (¬ p50) ∨ (¬ p134) ∨ (¬ p25) ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p50 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p25 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17117 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step31640 (p41 p45 p125 p135 p265 p420 p580 p601 : Prop)
    (h26831 : p45 ∨ p41)
    (h26881 : p601 ∨ p420)
    (h17400 : (¬ p45) ∨ (¬ p125) ∨ (¬ p135) ∨ (¬ p265) ∨ (¬ p580) ∨ (¬ p601)) : (¬ p125) ∨ (¬ p265) ∨ (¬ p580) ∨ p41 ∨ p420 ∨ (¬ p135) := by
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
  have u2 : p580 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17400 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)

theorem step31642 (p10 p101 p102 p136 p189 p258 : Prop)
    (h26837 : p102 ∨ p101)
    (h21008 : (¬ p10) ∨ (¬ p102) ∨ (¬ p136) ∨ (¬ p189) ∨ (¬ p258)) : (¬ p258) ∨ (¬ p189) ∨ p101 ∨ (¬ p136) ∨ (¬ p10) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p136 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h21008 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)

theorem step31643 (p10 p101 p102 p349 : Prop)
    (h26837 : p102 ∨ p101)
    (h9360 : (¬ p10) ∨ (¬ p102) ∨ (¬ p349)) : (¬ p10) ∨ p101 ∨ (¬ p349) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p101) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h9360 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)

theorem step31644 (p4 p10 p101 p102 p124 p304 p734 : Prop)
    (h26859 : p304 ∨ p124)
    (h26837 : p102 ∨ p101)
    (h16707 : (¬ p4) ∨ (¬ p10) ∨ (¬ p102) ∨ (¬ p304) ∨ (¬ p734)) : (¬ p10) ∨ p124 ∨ (¬ p4) ∨ (¬ p734) ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16707 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)

theorem step31645 (p2 p10 p50 p68 p134 p419 p431 p438 p481 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h26873 : p481 ∨ p2)
    (h17017 : (¬ p10) ∨ (¬ p50) ∨ (¬ p68) ∨ (¬ p134) ∨ (¬ p431) ∨ (¬ p438) ∨ (¬ p481) ∨ (¬ p996)) : (¬ p50) ∨ (¬ p10) ∨ (¬ p134) ∨ (¬ p68) ∨ (¬ p431) ∨ p419 ∨ (¬ p438) ∨ p2 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p50 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u9 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h17017 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u8)

theorem step31646 (p10 p125 p207 p362 : Prop)
    (h26865 : p362 ∨ p125)
    (h12470 : (¬ p10) ∨ (¬ p207) ∨ (¬ p362)) : (¬ p10) ∨ p125 ∨ (¬ p207) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p125) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h12470 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)

theorem step31647 (p10 p17 p126 p189 p256 : Prop)
    (h26853 : p256 ∨ p17)
    (h17669 : (¬ p10) ∨ (¬ p126) ∨ (¬ p189) ∨ (¬ p256)) : (¬ p10) ∨ (¬ p126) ∨ (¬ p189) ∨ p17 := by
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
  have u3 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17669 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step31648 (p10 p41 p45 p125 p262 p362 p576 p581 : Prop)
    (h26865 : p362 ∨ p125)
    (h26831 : p45 ∨ p41)
    (h26879 : p581 ∨ p576)
    (h17691 : (¬ p10) ∨ (¬ p45) ∨ (¬ p262) ∨ (¬ p362) ∨ (¬ p581)) : (¬ p10) ∨ p125 ∨ (¬ p262) ∨ p41 ∨ p576 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p125) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17691 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)

theorem step31649 (p10 p101 p102 p224 p303 p657 : Prop)
    (h26887 : p657 ∨ p224)
    (h26837 : p102 ∨ p101)
    (h17893 : (¬ p10) ∨ (¬ p102) ∨ (¬ p303) ∨ (¬ p657)) : (¬ p303) ∨ (¬ p10) ∨ p224 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17893 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)

theorem step31650 (p10 p101 p102 p125 p362 p1076 p1077 : Prop)
    (h26865 : p362 ∨ p125)
    (h26837 : p102 ∨ p101)
    (h26911 : p1077 ∨ p1076)
    (h17908 : (¬ p10) ∨ (¬ p102) ∨ (¬ p362) ∨ (¬ p1077)) : (¬ p10) ∨ p125 ∨ p101 ∨ p1076 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p125) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17908 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)

theorem step31651 (p10 p101 p102 p303 p1325 : Prop)
    (h26837 : p102 ∨ p101)
    (h18081 : (¬ p10) ∨ (¬ p102) ∨ (¬ p303) ∨ (¬ p1325)) : (¬ p10) ∨ (¬ p303) ∨ p101 ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18081 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)

theorem step31652 (p10 p101 p102 p124 p303 p304 : Prop)
    (h26859 : p304 ∨ p124)
    (h26837 : p102 ∨ p101)
    (h18375 : (¬ p10) ∨ (¬ p102) ∨ (¬ p303) ∨ (¬ p304)) : (¬ p10) ∨ p124 ∨ p101 ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18375 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step31653 (p10 p124 p125 p134 p304 p362 : Prop)
    (h26865 : p362 ∨ p125)
    (h26859 : p304 ∨ p124)
    (h18608 : (¬ p10) ∨ (¬ p134) ∨ (¬ p304) ∨ (¬ p362)) : p125 ∨ p124 ∨ (¬ p134) ∨ (¬ p10) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p125) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18608 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step31654 (p10 p125 p362 p961 p1210 p1346 p1465 p1508 : Prop)
    (h26865 : p362 ∨ p125)
    (h18779 : (¬ p10) ∨ (¬ p362) ∨ (¬ p961) ∨ (¬ p1210) ∨ (¬ p1346) ∨ (¬ p1465) ∨ (¬ p1508)) : (¬ p961) ∨ (¬ p1508) ∨ p125 ∨ (¬ p10) ∨ (¬ p1346) ∨ (¬ p1210) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18779 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u1)

theorem step31657 (p10 p101 p102 p224 p344 p657 : Prop)
    (h26887 : p657 ∨ p224)
    (h26837 : p102 ∨ p101)
    (h19568 : (¬ p10) ∨ (¬ p102) ∨ (¬ p344) ∨ (¬ p657)) : p224 ∨ (¬ p10) ∨ (¬ p344) ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p224) := fun hu => hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19568 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step31658 (p3 p10 p14 p125 p211 p226 p362 : Prop)
    (h26847 : p226 ∨ p3)
    (h26865 : p362 ∨ p125)
    (h19602 : (¬ p10) ∨ (¬ p14) ∨ (¬ p211) ∨ (¬ p226) ∨ (¬ p362)) : p3 ∨ (¬ p10) ∨ (¬ p211) ∨ (¬ p14) ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19602 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)

theorem step31659 (p10 p101 p102 p125 p185 p224 p263 p362 p836 : Prop)
    (h26865 : p362 ∨ p125)
    (h26837 : p102 ∨ p101)
    (h19629 : (¬ p10) ∨ (¬ p102) ∨ (¬ p185) ∨ (¬ p224) ∨ (¬ p263) ∨ (¬ p362) ∨ (¬ p836)) : (¬ p10) ∨ (¬ p185) ∨ (¬ p263) ∨ (¬ p836) ∨ (¬ p224) ∨ p125 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p263 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u8 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19629 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step31661 (p10 p101 p102 p125 p362 p496 p980 p1074 p1096 p1099 : Prop)
    (h26865 : p362 ∨ p125)
    (h26913 : p1099 ∨ p1096)
    (h26837 : p102 ∨ p101)
    (h19650 : (¬ p10) ∨ (¬ p102) ∨ (¬ p362) ∨ (¬ p496) ∨ (¬ p980) ∨ (¬ p1074) ∨ (¬ p1099)) : (¬ p10) ∨ p125 ∨ p1096 ∨ p101 ∨ (¬ p980) ∨ (¬ p1074) ∨ (¬ p496) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p125) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19650 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u8)

theorem step31664 (p10 p125 p134 p195 p211 p362 : Prop)
    (h26865 : p362 ∨ p125)
    (h20435 : (¬ p10) ∨ (¬ p134) ∨ (¬ p195) ∨ (¬ p211) ∨ (¬ p362)) : (¬ p10) ∨ p125 ∨ (¬ p211) ∨ (¬ p134) ∨ (¬ p195) := by
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
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20435 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step31665 (p10 p17 p101 p102 p126 p256 : Prop)
    (h26837 : p102 ∨ p101)
    (h26853 : p256 ∨ p17)
    (h20437 : (¬ p10) ∨ (¬ p102) ∨ (¬ p126) ∨ (¬ p256)) : (¬ p10) ∨ (¬ p126) ∨ p101 ∨ p17 := by
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
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20437 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)

theorem step31666 (p5 p10 p41 p101 p102 p124 p206 p304 p382 p406 p620 p1287 p1387 : Prop)
    (h26869 : p406 ∨ p382)
    (h26837 : p102 ∨ p101)
    (h26859 : p304 ∨ p124)
    (h20604 : (¬ p5) ∨ (¬ p10) ∨ (¬ p41) ∨ (¬ p102) ∨ (¬ p206) ∨ (¬ p304) ∨ (¬ p406) ∨ (¬ p620) ∨ (¬ p1287) ∨ (¬ p1387)) : p382 ∨ (¬ p41) ∨ p101 ∨ (¬ p1287) ∨ (¬ p5) ∨ p124 ∨ (¬ p620) ∨ (¬ p10) ∨ (¬ p206) ∨ (¬ p1387) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p620 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u11 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u12 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20604 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u12)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u3)
  · exact False.elim (q9 u9)

theorem step31667 (p5 p6 p8 p9 p10 p224 p517 p657 p789 p858 : Prop)
    (h26897 : p858 ∨ p789)
    (h26887 : p657 ∨ p224)
    (h20650 : (¬ p5) ∨ (¬ p6) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p517) ∨ (¬ p657) ∨ (¬ p858)) : (¬ p517) ∨ p789 ∨ (¬ p6) ∨ (¬ p10) ∨ (¬ p9) ∨ (¬ p8) ∨ (¬ p5) ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p517 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p789) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p9 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h20650 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u8)

theorem step31668 (p6 p10 p185 p194 p237 p303 p665 p1115 p1116 : Prop)
    (h26851 : p237 ∨ p185)
    (h26915 : p1116 ∨ p1115)
    (h16491 : (¬ p6) ∨ (¬ p10) ∨ (¬ p194) ∨ (¬ p237) ∨ (¬ p303) ∨ (¬ p665) ∨ (¬ p1116)) : (¬ p303) ∨ (¬ p10) ∨ (¬ p6) ∨ (¬ p665) ∨ p185 ∨ (¬ p194) ∨ p1115 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u8 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h16491 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u8)

theorem step31669 (p10 p18 p72 p125 p211 p362 : Prop)
    (h26865 : p362 ∨ p125)
    (h17883 : (¬ p10) ∨ (¬ p18) ∨ (¬ p72) ∨ (¬ p211) ∨ (¬ p362)) : (¬ p10) ∨ p125 ∨ (¬ p18) ∨ (¬ p72) ∨ (¬ p211) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p125) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p72 := by
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
  rcases h17883 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)

theorem step31670 (p5 p6 p10 p63 p303 p836 p840 p918 p928 : Prop)
    (h26901 : p928 ∨ p918)
    (h26895 : p840 ∨ p836)
    (h20351 : (¬ p5) ∨ (¬ p6) ∨ (¬ p10) ∨ (¬ p63) ∨ (¬ p303) ∨ (¬ p840) ∨ (¬ p928)) : (¬ p10) ∨ (¬ p303) ∨ p918 ∨ (¬ p63) ∨ (¬ p5) ∨ (¬ p6) ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20351 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u7)

theorem step31674 (p10 p323 p325 p329 : Prop)
    (h26860 : (¬ p10) ∨ (¬ p323))
    (h21607 : p329 ∨ p323 ∨ p325) : p325 ∨ p329 ∨ (¬ p10) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p325) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p329) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p323) := by
    rcases h26860 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h21607 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (u0 q2)

theorem step31699 (p17 p256 p264 : Prop)
    (h26852 : (¬ p17) ∨ (¬ p256))
    (h21163 : p264 ∨ p256) : p264 ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p264) := fun hu => hn (Or.inl hu)
  have u1 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p256) := by
    rcases h26852 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h21163 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step31700 (p17 p41 p126 p189 p256 : Prop)
    (h26853 : p256 ∨ p17)
    (h19251 : (¬ p41) ∨ (¬ p126) ∨ (¬ p189) ∨ (¬ p256)) : p17 ∨ (¬ p41) ∨ (¬ p126) ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p17) := fun hu => hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19251 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step31728 (p106 p169 p185 p237 p1076 p1077 p1118 p1349 : Prop)
    (h26851 : p237 ∨ p185)
    (h26911 : p1077 ∨ p1076)
    (h20045 : (¬ p106) ∨ (¬ p169) ∨ (¬ p237) ∨ (¬ p1077) ∨ (¬ p1118) ∨ (¬ p1349)) : (¬ p1349) ∨ p185 ∨ p1076 ∨ (¬ p106) ∨ (¬ p169) ∨ (¬ p1118) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p169 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1118 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20045 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u0)

theorem step31729 (p41 p45 p84 p169 p185 p225 p237 p303 p434 p544 p690 p819 : Prop)
    (h26877 : p544 ∨ p225)
    (h26851 : p237 ∨ p185)
    (h26831 : p45 ∨ p41)
    (h26132 : (¬ p690) ∨ (¬ p237) ∨ (¬ p84) ∨ (¬ p303) ∨ (¬ p434) ∨ (¬ p169) ∨ (¬ p45) ∨ (¬ p544) ∨ (¬ p819)) : (¬ p434) ∨ p225 ∨ (¬ p819) ∨ (¬ p303) ∨ (¬ p169) ∨ p185 ∨ (¬ p690) ∨ p41 ∨ (¬ p84) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p819 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p169 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p84 := by
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
    · exact False.elim (u5 q1)
  have u11 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h26132 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u11)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u2)

theorem step31730 (p125 p135 p169 p185 p189 p225 p237 p265 p303 p544 p1325 : Prop)
    (h26877 : p544 ∨ p225)
    (h26851 : p237 ∨ p185)
    (h19330 : (¬ p125) ∨ (¬ p135) ∨ (¬ p169) ∨ (¬ p189) ∨ (¬ p237) ∨ (¬ p265) ∨ (¬ p303) ∨ (¬ p544) ∨ (¬ p1325)) : (¬ p125) ∨ p225 ∨ (¬ p189) ∨ (¬ p169) ∨ p185 ∨ (¬ p135) ∨ (¬ p1325) ∨ (¬ p265) ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p169 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p303 := by
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
    · exact False.elim (u4 q1)
  rcases h19330 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u6)

theorem step31731 (p109 p134 p169 p185 p189 p237 : Prop)
    (h26851 : p237 ∨ p185)
    (h17074 : (¬ p109) ∨ (¬ p134) ∨ (¬ p169) ∨ (¬ p189) ∨ (¬ p237)) : (¬ p109) ∨ p185 ∨ (¬ p169) ∨ (¬ p134) ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p109 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p169 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17074 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)

theorem step31732 (p6 p41 p45 p109 p169 p192 p918 p928 : Prop)
    (h26831 : p45 ∨ p41)
    (h26901 : p928 ∨ p918)
    (h18547 : (¬ p6) ∨ (¬ p45) ∨ (¬ p109) ∨ (¬ p169) ∨ (¬ p192) ∨ (¬ p928)) : (¬ p192) ∨ p41 ∨ (¬ p169) ∨ (¬ p109) ∨ p918 ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p41) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p169 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p109 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18547 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u7)

theorem step31733 (p163 p224 p419 p424 p657 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h26887 : p657 ∨ p224)
    (h16983 : (¬ p163) ∨ (¬ p419) ∨ (¬ p657) ∨ (¬ p796)) : p424 ∨ (¬ p163) ∨ p224 ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16983 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step31734 (p163 p419 p424 p796 p1325 : Prop)
    (h26891 : p796 ∨ p424)
    (h18832 : (¬ p163) ∨ (¬ p419) ∨ (¬ p796) ∨ (¬ p1325)) : p424 ∨ (¬ p163) ∨ (¬ p419) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p163 := by
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
  have u4 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h18832 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)

theorem step31735 (p109 p163 p207 p368 p382 p406 p789 p797 p858 : Prop)
    (h26869 : p406 ∨ p382)
    (h26897 : p858 ∨ p789)
    (h18854 : (¬ p109) ∨ (¬ p163) ∨ (¬ p207) ∨ (¬ p368) ∨ (¬ p406) ∨ (¬ p797) ∨ (¬ p858)) : (¬ p797) ∨ p382 ∨ p789 ∨ (¬ p109) ∨ (¬ p163) ∨ (¬ p368) ∨ (¬ p207) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p797 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p109 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18854 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u8)

theorem step31736 (p12 p86 p163 p189 p193 p595 p616 p665 p1287 : Prop)
    (h26845 : p193 ∨ p189)
    (h26883 : p616 ∨ p595)
    (h18099 : (¬ p12) ∨ (¬ p86) ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p616) ∨ (¬ p665) ∨ (¬ p1287)) : (¬ p12) ∨ p189 ∨ (¬ p163) ∨ (¬ p665) ∨ (¬ p86) ∨ p595 ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18099 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step31739 (p14 p15 p63 p69 p163 p229 : Prop)
    (h26849 : p229 ∨ p14)
    (h26833 : p69 ∨ p15)
    (h19109 : (¬ p63) ∨ (¬ p69) ∨ (¬ p163) ∨ (¬ p229)) : p14 ∨ p15 ∨ (¬ p63) ∨ (¬ p163) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19109 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step31740 (p109 p125 p126 p136 p163 p207 p301 p362 : Prop)
    (h26857 : p301 ∨ p126)
    (h26865 : p362 ∨ p125)
    (h19417 : (¬ p109) ∨ (¬ p136) ∨ (¬ p163) ∨ (¬ p207) ∨ (¬ p301) ∨ (¬ p362)) : p126 ∨ (¬ p163) ∨ p125 ∨ (¬ p207) ∨ (¬ p136) ∨ (¬ p109) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p136 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p109 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19417 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)

theorem step31741 (p86 p163 p189 p193 p225 p351 p420 p495 p544 : Prop)
    (h26877 : p544 ∨ p225)
    (h26845 : p193 ∨ p189)
    (h16225 : (¬ p86) ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p351) ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p544)) : (¬ p420) ∨ (¬ p351) ∨ (¬ p86) ∨ p225 ∨ p189 ∨ (¬ p163) ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16225 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step31743 (p8 p48 p163 p305 p344 p422 p423 p425 p582 p710 p1076 : Prop)
    (h26889 : p710 ∨ p8)
    (h18752 : (¬ p48) ∨ (¬ p163) ∨ (¬ p305) ∨ (¬ p344) ∨ (¬ p422) ∨ (¬ p423) ∨ (¬ p425) ∨ (¬ p582) ∨ (¬ p710) ∨ (¬ p1076)) : (¬ p305) ∨ (¬ p422) ∨ (¬ p425) ∨ (¬ p1076) ∨ p8 ∨ (¬ p48) ∨ (¬ p344) ∨ (¬ p582) ∨ (¬ p423) ∨ (¬ p163) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18752 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u10)
  · exact False.elim (q9 u3)

theorem step31745 (p124 p163 p189 p193 p225 p267 p304 p544 p664 p1076 : Prop)
    (h26859 : p304 ∨ p124)
    (h26877 : p544 ∨ p225)
    (h26845 : p193 ∨ p189)
    (h18753 : (¬ p163) ∨ (¬ p193) ∨ (¬ p267) ∨ (¬ p304) ∨ (¬ p544) ∨ (¬ p664) ∨ (¬ p1076)) : p124 ∨ (¬ p1076) ∨ (¬ p664) ∨ (¬ p163) ∨ p225 ∨ (¬ p267) ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p1076 := by
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
  have u4 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p267 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18753 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u1)

theorem step31746 (p48 p124 p163 p304 p425 p582 p980 p1076 p1711 p1712 : Prop)
    (h26859 : p304 ∨ p124)
    (h18743 : (¬ p48) ∨ (¬ p163) ∨ (¬ p304) ∨ (¬ p425) ∨ (¬ p582) ∨ (¬ p980) ∨ (¬ p1076) ∨ (¬ p1711) ∨ (¬ p1712)) : (¬ p1711) ∨ (¬ p1712) ∨ (¬ p48) ∨ (¬ p163) ∨ (¬ p425) ∨ (¬ p1076) ∨ p124 ∨ (¬ p582) ∨ (¬ p980) := by
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
  have u2 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p582 := by
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
    · exact False.elim (u6 q1)
  rcases h18743 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u0)
  · exact False.elim (q8 u1)

theorem step31747 (p86 p163 p186 p224 p422 p897 p1096 p1099 p1140 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h16982 : (¬ p86) ∨ (¬ p163) ∨ (¬ p186) ∨ (¬ p224) ∨ (¬ p422) ∨ (¬ p897) ∨ (¬ p1099) ∨ (¬ p1140)) : (¬ p422) ∨ (¬ p1140) ∨ (¬ p186) ∨ (¬ p224) ∨ (¬ p897) ∨ (¬ p163) ∨ (¬ p86) ∨ p1096 := by
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
  have u2 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h16982 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u1)

theorem step31749 (p3 p163 p188 p226 p790 : Prop)
    (h26847 : p226 ∨ p3)
    (h26133 : (¬ p790) ∨ (¬ p226) ∨ (¬ p163) ∨ (¬ p188)) : p3 ∨ (¬ p790) ∨ (¬ p163) ∨ (¬ p188) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p790 := by
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
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h26133 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)

theorem step31750 (p3 p17 p135 p163 p188 p226 p256 : Prop)
    (h26847 : p226 ∨ p3)
    (h26853 : p256 ∨ p17)
    (h19243 : (¬ p135) ∨ (¬ p163) ∨ (¬ p188) ∨ (¬ p226) ∨ (¬ p256)) : p3 ∨ p17 ∨ (¬ p163) ∨ (¬ p188) ∨ (¬ p135) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19243 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)

theorem step31751 (p3 p64 p86 p163 p189 p193 p226 : Prop)
    (h26847 : p226 ∨ p3)
    (h26845 : p193 ∨ p189)
    (h17209 : (¬ p64) ∨ (¬ p86) ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p226)) : p3 ∨ p189 ∨ (¬ p86) ∨ (¬ p64) ∨ (¬ p163) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17209 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step31753 (p86 p106 p125 p163 p189 p193 p420 p494 p601 p633 p636 : Prop)
    (h26885 : p636 ∨ p633)
    (h26845 : p193 ∨ p189)
    (h26881 : p601 ∨ p420)
    (h17043 : (¬ p86) ∨ (¬ p106) ∨ (¬ p125) ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p494) ∨ (¬ p601) ∨ (¬ p636)) : (¬ p125) ∨ p633 ∨ (¬ p163) ∨ p189 ∨ (¬ p494) ∨ (¬ p86) ∨ p420 ∨ (¬ p106) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p633) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h17043 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u8)

theorem step31754 (p86 p106 p163 p189 p193 p455 p494 p633 p636 p961 : Prop)
    (h26845 : p193 ∨ p189)
    (h26885 : p636 ∨ p633)
    (h17048 : (¬ p86) ∨ (¬ p106) ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p455) ∨ (¬ p494) ∨ (¬ p636) ∨ (¬ p961)) : (¬ p961) ∨ (¬ p494) ∨ (¬ p163) ∨ (¬ p106) ∨ (¬ p455) ∨ (¬ p86) ∨ p189 ∨ p633 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p633) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h17048 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u0)

theorem step31760 (p1 p2 p163 p167 p192 : Prop)
    (h26842 : (¬ p163) ∨ (¬ p167))
    (h13399 : (¬ p1) ∨ (¬ p2) ∨ p167 ∨ (¬ p192)) : (¬ p2) ∨ (¬ p192) ∨ (¬ p1) ∨ (¬ p163) := by
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
  have u2 : p1 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p167) := by
    rcases h26842 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h13399 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (u4 q2)
  · exact False.elim (q3 u1)

theorem step31786 (p1 p2 p3 p226 : Prop)
    (h26846 : (¬ p3) ∨ (¬ p226))
    (h11951 : (¬ p1) ∨ (¬ p2) ∨ p226) : (¬ p3) ∨ (¬ p1) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p226) := by
    rcases h26846 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h11951 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (u3 q2)

theorem step31787 (p2 p3 p224 p419 p657 : Prop)
    (h26887 : p657 ∨ p224)
    (h16553 : (¬ p2) ∨ (¬ p3) ∨ (¬ p419) ∨ (¬ p657)) : (¬ p2) ∨ p224 ∨ (¬ p3) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16553 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step31790 (p2 p3 p163 p167 p303 p331 p495 p499 p600 p1286 : Prop)
    (h26875 : p499 ∨ p495)
    (h26843 : p167 ∨ p163)
    (h18545 : (¬ p2) ∨ (¬ p3) ∨ (¬ p167) ∨ (¬ p303) ∨ (¬ p331) ∨ (¬ p499) ∨ (¬ p600) ∨ (¬ p1286)) : (¬ p1286) ∨ p495 ∨ (¬ p331) ∨ (¬ p600) ∨ (¬ p3) ∨ (¬ p303) ∨ p163 ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p331 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p600 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18545 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u0)

theorem step31791 (p3 p163 p167 p1140 p1159 p1465 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26843 : p167 ∨ p163)
    (h18589 : (¬ p3) ∨ (¬ p167) ∨ (¬ p1159) ∨ (¬ p1465)) : p1140 ∨ (¬ p3) ∨ p163 ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18589 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)

theorem step31792 (p3 p163 p167 p532 p1140 p1159 p1214 p1346 p1508 : Prop)
    (h26843 : p167 ∨ p163)
    (h26919 : p1159 ∨ p1140)
    (h18596 : (¬ p3) ∨ (¬ p167) ∨ (¬ p532) ∨ (¬ p1159) ∨ (¬ p1214) ∨ (¬ p1346) ∨ (¬ p1508)) : (¬ p1508) ∨ p163 ∨ (¬ p1346) ∨ p1140 ∨ (¬ p1214) ∨ (¬ p532) ∨ (¬ p3) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1214 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18596 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u0)

theorem step31793 (p3 p14 p63 p229 p789 p1004 p1140 p1159 p1385 p1393 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26849 : p229 ∨ p14)
    (h26933 : p1393 ∨ p1385)
    (h19383 : (¬ p3) ∨ (¬ p63) ∨ (¬ p229) ∨ (¬ p789) ∨ (¬ p1004) ∨ (¬ p1159) ∨ (¬ p1393)) : p1140 ∨ (¬ p1004) ∨ p14 ∨ (¬ p63) ∨ p1385 ∨ (¬ p3) ∨ (¬ p789) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19383 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u9)

theorem step31796 (p3 p18 p72 p124 p210 p304 p344 p346 p668 p880 p1095 : Prop)
    (h26859 : p304 ∨ p124)
    (h26863 : p346 ∨ p344)
    (h20571 : (¬ p3) ∨ (¬ p18) ∨ (¬ p72) ∨ (¬ p210) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p668) ∨ (¬ p880) ∨ (¬ p1095)) : (¬ p210) ∨ p124 ∨ (¬ p880) ∨ (¬ p668) ∨ (¬ p18) ∨ (¬ p1095) ∨ (¬ p72) ∨ (¬ p3) ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p880 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h20571 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u2)
  · exact False.elim (q8 u5)

theorem step31797 (p3 p14 p16 p18 p19 p71 p229 p789 p790 p814 p858 p1325 : Prop)
    (h26849 : p229 ∨ p14)
    (h26893 : p814 ∨ p790)
    (h26897 : p858 ∨ p789)
    (h26829 : p19 ∨ p18)
    (h19198 : (¬ p3) ∨ (¬ p16) ∨ (¬ p19) ∨ (¬ p71) ∨ (¬ p229) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1325)) : p14 ∨ (¬ p3) ∨ (¬ p71) ∨ p790 ∨ p789 ∨ p18 ∨ (¬ p1325) ∨ (¬ p16) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19198 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u6)

theorem step31798 (p3 p14 p16 p71 p229 p789 p790 p814 p858 p1193 p1542 : Prop)
    (h26849 : p229 ∨ p14)
    (h26893 : p814 ∨ p790)
    (h26897 : p858 ∨ p789)
    (h26134 : (¬ p1542) ∨ (¬ p858) ∨ (¬ p229) ∨ (¬ p1193) ∨ (¬ p16) ∨ (¬ p3) ∨ (¬ p814) ∨ (¬ p71)) : (¬ p1542) ∨ p14 ∨ (¬ p1193) ∨ (¬ p71) ∨ (¬ p16) ∨ (¬ p3) ∨ p790 ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p14) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h26134 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u3)

theorem step31799 (p3 p39 p63 p68 p225 p544 p664 p1074 p1096 p1099 : Prop)
    (h26877 : p544 ∨ p225)
    (h26913 : p1099 ∨ p1096)
    (h19616 : (¬ p3) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p544) ∨ (¬ p664) ∨ (¬ p1074) ∨ (¬ p1099)) : (¬ p68) ∨ p225 ∨ (¬ p63) ∨ (¬ p3) ∨ (¬ p39) ∨ (¬ p664) ∨ (¬ p1074) ∨ p1096 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p39 := by
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
  have u7 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h19616 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u9)

theorem step31800 (p3 p39 p63 p68 p224 p225 p544 p657 p864 p1229 p1232 p1269 : Prop)
    (h26877 : p544 ∨ p225)
    (h26927 : p1232 ∨ p1229)
    (h26887 : p657 ∨ p224)
    (h20473 : (¬ p3) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p544) ∨ (¬ p657) ∨ (¬ p864) ∨ (¬ p1232) ∨ (¬ p1269)) : (¬ p864) ∨ p225 ∨ (¬ p3) ∨ (¬ p68) ∨ p1229 ∨ (¬ p63) ∨ (¬ p39) ∨ (¬ p1269) ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p864 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1269 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h20473 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u7)

theorem step31801 (p3 p72 p224 p234 p435 p657 p680 p687 p880 p897 p904 p1187 : Prop)
    (h26887 : p657 ∨ p224)
    (h26899 : p904 ∨ p897)
    (h26921 : p1187 ∨ p234)
    (h20582 : (¬ p3) ∨ (¬ p72) ∨ (¬ p435) ∨ (¬ p657) ∨ (¬ p680) ∨ (¬ p687) ∨ (¬ p880) ∨ (¬ p904) ∨ (¬ p1187)) : (¬ p687) ∨ (¬ p880) ∨ p224 ∨ p897 ∨ (¬ p3) ∨ (¬ p72) ∨ (¬ p435) ∨ p234 ∨ (¬ p680) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p880 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p234) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h20582 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u11)

theorem step31802 (p3 p6 p121 p163 p167 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26843 : p167 ∨ p163)
    (h16966 : (¬ p3) ∨ (¬ p6) ∨ (¬ p167) ∨ (¬ p1206)) : p121 ∨ (¬ p3) ∨ (¬ p6) ∨ p163 := by
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
  have u3 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16966 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step31804 (p3 p10 p14 p25 p229 p420 p601 : Prop)
    (h26881 : p601 ∨ p420)
    (h26849 : p229 ∨ p14)
    (h18224 : (¬ p3) ∨ (¬ p10) ∨ (¬ p25) ∨ (¬ p229) ∨ (¬ p601)) : (¬ p10) ∨ p420 ∨ (¬ p25) ∨ p14 ∨ (¬ p3) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p420) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p25 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18224 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step31805 (p3 p12 p24 p124 p134 p195 p304 p344 p346 p425 p668 : Prop)
    (h26859 : p304 ∨ p124)
    (h26863 : p346 ∨ p344)
    (h20411 : (¬ p3) ∨ (¬ p12) ∨ (¬ p24) ∨ (¬ p134) ∨ (¬ p195) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p425) ∨ (¬ p668)) : p124 ∨ (¬ p24) ∨ (¬ p195) ∨ (¬ p3) ∨ (¬ p668) ∨ (¬ p134) ∨ (¬ p12) ∨ (¬ p425) ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p24 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h20411 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u4)

theorem step31806 (p3 p225 p544 p664 p1038 p1140 p1159 : Prop)
    (h26877 : p544 ∨ p225)
    (h26919 : p1159 ∨ p1140)
    (h16917 : (¬ p3) ∨ (¬ p544) ∨ (¬ p664) ∨ (¬ p1038) ∨ (¬ p1159)) : (¬ p1038) ∨ p225 ∨ p1140 ∨ (¬ p664) ∨ (¬ p3) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1038 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16917 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u6)

theorem step31807 (p3 p86 p163 p167 p186 p422 p595 p616 p1000 p1256 p1287 : Prop)
    (h26843 : p167 ∨ p163)
    (h26929 : p1256 ∨ p422)
    (h26883 : p616 ∨ p595)
    (h17294 : (¬ p3) ∨ (¬ p86) ∨ (¬ p167) ∨ (¬ p186) ∨ (¬ p616) ∨ (¬ p1000) ∨ (¬ p1256) ∨ (¬ p1287)) : p163 ∨ p422 ∨ (¬ p1287) ∨ (¬ p86) ∨ (¬ p1000) ∨ (¬ p186) ∨ p595 ∨ (¬ p3) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p163) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p422) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h17294 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u2)

theorem step31808 (p189 p191 p193 : Prop)
    (h26845 : p193 ∨ p189)
    (h17914 : p191 ∨ (¬ p193)) : p191 ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p191) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr hu)
  have u2 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17914 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)

theorem step31810 (p189 p193 p419 p789 p790 p814 p858 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h26893 : p814 ∨ p790)
    (h26845 : p193 ∨ p189)
    (h26897 : p858 ∨ p789)
    (h16527 : (¬ p193) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p996)) : p419 ∨ p790 ∨ p189 ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p790) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16527 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u4)

theorem step31812 (p2 p455 p456 p633 p1140 p1211 : Prop)
    (h26871 : p456 ∨ p455)
    (h19385 : (¬ p2) ∨ (¬ p456) ∨ (¬ p633) ∨ (¬ p1140) ∨ (¬ p1211)) : (¬ p2) ∨ (¬ p1140) ∨ (¬ p633) ∨ (¬ p1211) ∨ p455 := by
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
  have u2 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p455) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19385 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)

theorem step31813 (p121 p1206 p1207 p1211 : Prop)
    (h26922 : (¬ p121) ∨ (¬ p1206))
    (h21629 : p1211 ∨ p1207 ∨ p1206) : p1211 ∨ p1207 ∨ (¬ p121) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1211) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1207) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1206) := by
    rcases h26922 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h21629 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (u3 q2)

theorem step31814 (p121 p207 p961 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h9305 : (¬ p207) ∨ p961 ∨ (¬ p1206)) : p961 ∨ p121 ∨ (¬ p207) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p961) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p121) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h9305 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)

theorem step31815 (p121 p125 p331 p362 p419 p789 p790 p814 p858 p961 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h26865 : p362 ∨ p125)
    (h26897 : p858 ∨ p789)
    (h26893 : p814 ∨ p790)
    (h18991 : (¬ p121) ∨ (¬ p331) ∨ (¬ p362) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p961) ∨ (¬ p996)) : p419 ∨ (¬ p961) ∨ p125 ∨ (¬ p331) ∨ (¬ p121) ∨ p789 ∨ p790 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p331 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18991 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step31816 (p6 p41 p121 p127 p187 p1452 : Prop)
    (h26839 : p127 ∨ p6)
    (h17575 : (¬ p41) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p187) ∨ (¬ p1452)) : (¬ p1452) ∨ (¬ p41) ∨ (¬ p121) ∨ p6 ∨ (¬ p187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17575 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u0)

theorem step31817 (p6 p8 p41 p121 p127 p187 p710 p897 p904 p1074 p1081 p1097 : Prop)
    (h26839 : p127 ∨ p6)
    (h26899 : p904 ∨ p897)
    (h26889 : p710 ∨ p8)
    (h20339 : (¬ p41) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p187) ∨ (¬ p710) ∨ (¬ p904) ∨ (¬ p1074) ∨ (¬ p1081) ∨ (¬ p1097)) : p6 ∨ (¬ p1081) ∨ (¬ p1074) ∨ (¬ p121) ∨ (¬ p1097) ∨ p897 ∨ (¬ p41) ∨ (¬ p187) ∨ p8 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p6) := fun hu => hn (Or.inl hu)
  have u1 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1097 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u11 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h20339 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u4)

theorem step31818 (p101 p102 p121 p1078 : Prop)
    (h26836 : (¬ p101) ∨ (¬ p102))
    (h9381 : p102 ∨ (¬ p121) ∨ (¬ p1078)) : (¬ p1078) ∨ (¬ p121) ∨ (¬ p101) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1078 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p102) := by
    rcases h26836 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h9381 with q0 | q1 | q2
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)

theorem step31820 (p8 p121 p210 p305 p344 p710 p1084 : Prop)
    (h26889 : p710 ∨ p8)
    (h17057 : (¬ p121) ∨ (¬ p210) ∨ (¬ p305) ∨ (¬ p344) ∨ (¬ p710) ∨ (¬ p1084)) : (¬ p305) ∨ (¬ p344) ∨ (¬ p121) ∨ (¬ p1084) ∨ (¬ p210) ∨ p8 := by
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
  have u2 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17057 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)

theorem step31821 (p3 p6 p104 p121 p127 p226 p1084 : Prop)
    (h26847 : p226 ∨ p3)
    (h26839 : p127 ∨ p6)
    (h20574 : (¬ p104) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p226) ∨ (¬ p1084)) : p3 ∨ (¬ p104) ∨ (¬ p1084) ∨ (¬ p121) ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20574 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)

theorem step31822 (p11 p121 p140 p1443 : Prop)
    (h26934 : (¬ p11) ∨ (¬ p1443))
    (h15689 : (¬ p121) ∨ (¬ p140) ∨ p1443) : (¬ p11) ∨ (¬ p121) ∨ (¬ p140) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
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
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1443) := by
    rcases h26934 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h15689 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (u3 q2)

theorem step31823 (p6 p101 p102 p127 p1080 p1140 p1159 p1208 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26837 : p102 ∨ p101)
    (h26839 : p127 ∨ p6)
    (h19016 : (¬ p102) ∨ (¬ p127) ∨ (¬ p1080) ∨ (¬ p1159) ∨ (¬ p1208)) : (¬ p1208) ∨ p1140 ∨ p101 ∨ (¬ p1080) ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1208 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1140) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1080 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19016 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)

theorem step31825 (p5 p63 p1022 p1140 p1159 p1330 p1385 p1393 p1465 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h26919 : p1159 ∨ p1140)
    (h18426 : (¬ p5) ∨ (¬ p63) ∨ (¬ p1022) ∨ (¬ p1159) ∨ (¬ p1330) ∨ (¬ p1393) ∨ (¬ p1465)) : (¬ p1022) ∨ p1385 ∨ (¬ p1465) ∨ (¬ p1330) ∨ (¬ p63) ∨ (¬ p5) ∨ p1140 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1385) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18426 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u2)

theorem step31826 (p63 p64 p134 p422 p1140 p1159 p1256 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26929 : p1256 ∨ p422)
    (h19815 : (¬ p63) ∨ (¬ p64) ∨ (¬ p134) ∨ (¬ p1159) ∨ (¬ p1256)) : p1140 ∨ (¬ p64) ∨ p422 ∨ (¬ p134) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19815 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)

theorem step31827 (p6 p127 p1140 p1159 p1212 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26839 : p127 ∨ p6)
    (h12157 : (¬ p127) ∨ (¬ p1159) ∨ (¬ p1212)) : p1140 ∨ (¬ p1212) ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : p1212 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h12157 with q0 | q1 | q2
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)

theorem step31828 (p48 p64 p423 p929 p1096 p1140 p1159 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h18881 : (¬ p48) ∨ (¬ p64) ∨ (¬ p423) ∨ (¬ p929) ∨ (¬ p1096) ∨ (¬ p1159)) : p1140 ∨ (¬ p64) ∨ (¬ p423) ∨ (¬ p1096) ∨ (¬ p929) ∨ (¬ p48) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p929 := by
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
  rcases h18881 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)

theorem step31829 (p16 p188 p422 p424 p545 p796 p897 p904 p1096 p1140 p1159 p1256 : Prop)
    (h26891 : p796 ∨ p424)
    (h26919 : p1159 ∨ p1140)
    (h26929 : p1256 ∨ p422)
    (h26899 : p904 ∨ p897)
    (h18447 : (¬ p16) ∨ (¬ p188) ∨ (¬ p545) ∨ (¬ p796) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1159) ∨ (¬ p1256)) : p424 ∨ p1140 ∨ p422 ∨ (¬ p545) ∨ (¬ p1096) ∨ p897 ∨ (¬ p188) ∨ (¬ p16) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1140) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18447 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u10)

theorem step31830 (p18 p101 p423 p1140 p1159 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h19725 : (¬ p18) ∨ (¬ p101) ∨ (¬ p423) ∨ (¬ p1159)) : p1140 ∨ (¬ p423) ∨ (¬ p18) ∨ (¬ p101) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19725 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)

theorem step31831 (p5 p63 p860 p1140 p1159 p1273 p1325 p1333 p1465 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26919 : p1159 ∨ p1140)
    (h18240 : (¬ p5) ∨ (¬ p63) ∨ (¬ p860) ∨ (¬ p1159) ∨ (¬ p1273) ∨ (¬ p1333) ∨ (¬ p1465)) : p1325 ∨ (¬ p860) ∨ p1140 ∨ (¬ p63) ∨ (¬ p1273) ∨ (¬ p5) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1325) := fun hu => hn (Or.inl hu)
  have u1 : p860 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18240 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u6)

theorem step31832 (p101 p124 p211 p1140 p1159 p1209 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h20098 : (¬ p101) ∨ (¬ p124) ∨ (¬ p211) ∨ (¬ p1159) ∨ (¬ p1209)) : p1140 ∨ (¬ p101) ∨ (¬ p124) ∨ (¬ p211) ∨ (¬ p1209) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
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
  have u4 : p1209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h20098 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)

theorem step31834 (p101 p102 p1084 : Prop)
    (h26837 : p102 ∨ p101)
    (h19460 : (¬ p102) ∨ p1084) : p101 ∨ p1084 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p101) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1084) := fun hu => hn (Or.inr hu)
  have u2 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19460 with q0 | q1
  · exact False.elim (q0 u2)
  · exact False.elim (u1 q1)

theorem step31835 (p2 p6 p303 p419 p481 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h26873 : p481 ∨ p2)
    (h18047 : (¬ p6) ∨ (¬ p303) ∨ (¬ p481) ∨ (¬ p996)) : p419 ∨ (¬ p303) ∨ p2 ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18047 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step31836 (p6 p101 p224 p344 p346 : Prop)
    (h26863 : p346 ∨ p344)
    (h16370 : (¬ p6) ∨ (¬ p101) ∨ (¬ p224) ∨ (¬ p346)) : p344 ∨ (¬ p101) ∨ (¬ p224) ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p344) := fun hu => hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h16370 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step31837 (p6 p101 p224 p303 p345 p657 : Prop)
    (h26887 : p657 ∨ p224)
    (h17265 : (¬ p6) ∨ (¬ p101) ∨ (¬ p303) ∨ (¬ p345) ∨ (¬ p657)) : (¬ p101) ∨ (¬ p345) ∨ p224 ∨ (¬ p6) ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p345 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17265 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)

theorem step31838 (p6 p101 p344 p346 p734 : Prop)
    (h26863 : p346 ∨ p344)
    (h18925 : (¬ p6) ∨ (¬ p101) ∨ (¬ p346) ∨ (¬ p734)) : (¬ p101) ∨ p344 ∨ (¬ p734) ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18925 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)

theorem step31840 (p6 p17 p140 p188 p256 : Prop)
    (h26853 : p256 ∨ p17)
    (h9409 : (¬ p6) ∨ (¬ p140) ∨ (¬ p188) ∨ (¬ p256)) : p17 ∨ (¬ p188) ∨ (¬ p6) ∨ (¬ p140) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p17) := fun hu => hn (Or.inl hu)
  have u1 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h9409 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)

theorem step31842 (p6 p121 p532 p980 p983 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26903 : p983 ∨ p980)
    (h16341 : (¬ p6) ∨ (¬ p532) ∨ (¬ p983) ∨ (¬ p1206)) : p121 ∨ p980 ∨ (¬ p532) ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16341 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step31843 (p6 p41 p45 p121 p192 p532 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26831 : p45 ∨ p41)
    (h18959 : (¬ p6) ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p532) ∨ (¬ p1206)) : p121 ∨ p41 ∨ (¬ p532) ∨ (¬ p192) ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p41) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18959 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step31867 (p121 p1206 p1212 : Prop)
    (h26922 : (¬ p121) ∨ (¬ p1206))
    (h21957 : p1212 ∨ p1206) : p1212 ∨ (¬ p121) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1212) := fun hu => hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1206) := by
    rcases h26922 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h21957 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step31869 (p345 p438 p668 p728 p1076 p1077 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h17268 : (¬ p345) ∨ (¬ p438) ∨ (¬ p668) ∨ (¬ p728) ∨ (¬ p1077)) : (¬ p728) ∨ p1076 ∨ (¬ p668) ∨ (¬ p345) ∨ (¬ p438) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p345 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17268 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)

theorem step31870 (p125 p227 p383 p517 p789 p858 : Prop)
    (h26897 : p858 ∨ p789)
    (h16596 : (¬ p125) ∨ (¬ p227) ∨ (¬ p383) ∨ (¬ p517) ∨ (¬ p858)) : (¬ p517) ∨ (¬ p125) ∨ (¬ p227) ∨ p789 ∨ (¬ p383) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p517 := by
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
  have u3 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p383 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16596 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)

theorem step31872 (p124 p227 p304 p1078 : Prop)
    (h26859 : p304 ∨ p124)
    (h9382 : (¬ p227) ∨ (¬ p304) ∨ (¬ p1078)) : p124 ∨ (¬ p1078) ∨ (¬ p227) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p1078 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h9382 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)

theorem step31873 (p101 p102 p124 p227 p304 p1452 : Prop)
    (h26837 : p102 ∨ p101)
    (h26859 : p304 ∨ p124)
    (h18502 : (¬ p102) ∨ (¬ p227) ∨ (¬ p304) ∨ (¬ p1452)) : (¬ p227) ∨ (¬ p1452) ∨ p101 ∨ p124 := by
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
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18502 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)

theorem step31875 (p121 p207 p227 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h9048 : (¬ p207) ∨ (¬ p227) ∨ (¬ p1206)) : (¬ p227) ∨ p121 ∨ (¬ p207) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p121) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h9048 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)

theorem step31876 (p163 p167 p189 p227 p263 p940 p985 p1452 : Prop)
    (h26843 : p167 ∨ p163)
    (h18145 : (¬ p167) ∨ (¬ p189) ∨ (¬ p227) ∨ (¬ p263) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1452)) : (¬ p940) ∨ (¬ p1452) ∨ (¬ p227) ∨ (¬ p263) ∨ (¬ p985) ∨ p163 ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1452 := by
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
  have u4 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18145 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u1)

theorem step31878 (p18 p72 p121 p211 p227 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h20334 : (¬ p18) ∨ (¬ p72) ∨ (¬ p211) ∨ (¬ p227) ∨ (¬ p1206)) : p121 ∨ (¬ p227) ∨ (¬ p211) ∨ (¬ p18) ∨ (¬ p72) := by
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
  have u3 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h20334 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)

theorem step31879 (p11 p227 p262 p1443 : Prop)
    (h26934 : (¬ p11) ∨ (¬ p1443))
    (h13673 : (¬ p227) ∨ (¬ p262) ∨ p1443) : (¬ p227) ∨ (¬ p11) ∨ (¬ p262) := by
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
  have u2 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1443) := by
    rcases h26934 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h13673 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (u3 q2)

theorem step31880 (p8 p227 p305 p344 p710 p1084 : Prop)
    (h26889 : p710 ∨ p8)
    (h17056 : (¬ p227) ∨ (¬ p305) ∨ (¬ p344) ∨ (¬ p710) ∨ (¬ p1084)) : (¬ p305) ∨ (¬ p344) ∨ (¬ p1084) ∨ p8 ∨ (¬ p227) := by
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
  have u2 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17056 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)

theorem step31881 (p3 p14 p44 p83 p188 p226 p227 p496 p1452 p1473 p1711 : Prop)
    (h26847 : p226 ∨ p3)
    (h18979 : (¬ p14) ∨ (¬ p44) ∨ (¬ p83) ∨ (¬ p188) ∨ (¬ p226) ∨ (¬ p227) ∨ (¬ p496) ∨ (¬ p1452) ∨ (¬ p1473) ∨ (¬ p1711)) : (¬ p1711) ∨ p3 ∨ (¬ p14) ∨ (¬ p1452) ∨ (¬ p1473) ∨ (¬ p44) ∨ (¬ p188) ∨ (¬ p496) ∨ (¬ p83) ∨ (¬ p227) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1711 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1473 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18979 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u3)
  · exact False.elim (q8 u4)
  · exact False.elim (q9 u0)

theorem step31882 (p3 p11 p126 p194 p225 p226 p227 p266 p347 : Prop)
    (h26847 : p226 ∨ p3)
    (h18210 : (¬ p11) ∨ (¬ p126) ∨ (¬ p194) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p227) ∨ (¬ p266) ∨ (¬ p347)) : (¬ p11) ∨ (¬ p266) ∨ (¬ p225) ∨ (¬ p126) ∨ (¬ p194) ∨ p3 ∨ (¬ p227) ∨ (¬ p347) := by
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
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18210 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u7)

theorem step31883 (p124 p258 p262 p304 : Prop)
    (h26858 : (¬ p124) ∨ (¬ p304))
    (h13607 : (¬ p258) ∨ (¬ p262) ∨ p304) : (¬ p258) ∨ (¬ p124) ∨ (¬ p262) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p304) := by
    rcases h26858 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h13607 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (u3 q2)

theorem step31884 (p11 p121 p137 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h15482 : p11 ∨ (¬ p137) ∨ (¬ p1206)) : p121 ∨ p11 ∨ (¬ p137) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p11) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p137 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h15482 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)

theorem step31900 (p344 p346 p495 p836 p840 p926 p1096 : Prop)
    (h26863 : p346 ∨ p344)
    (h26895 : p840 ∨ p836)
    (h16635 : (¬ p346) ∨ (¬ p495) ∨ (¬ p840) ∨ (¬ p926) ∨ (¬ p1096)) : (¬ p1096) ∨ (¬ p926) ∨ p344 ∨ p836 ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p926 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16635 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)

theorem step31901 (p5 p6 p41 p89 p101 p344 p346 p790 p1385 : Prop)
    (h26863 : p346 ∨ p344)
    (h20643 : (¬ p5) ∨ (¬ p6) ∨ (¬ p41) ∨ (¬ p89) ∨ (¬ p101) ∨ (¬ p346) ∨ (¬ p790) ∨ (¬ p1385)) : (¬ p101) ∨ p344 ∨ (¬ p89) ∨ (¬ p790) ∨ (¬ p41) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20643 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u7)

theorem step31902 (p108 p124 p209 p225 p304 p344 p346 p544 : Prop)
    (h26859 : p304 ∨ p124)
    (h26863 : p346 ∨ p344)
    (h26877 : p544 ∨ p225)
    (h18825 : (¬ p108) ∨ (¬ p209) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p544)) : p124 ∨ p344 ∨ (¬ p108) ∨ p225 ∨ (¬ p209) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p209 := by
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
  have u7 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18825 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)

theorem step31904 (p101 p134 p189 p344 p346 : Prop)
    (h26863 : p346 ∨ p344)
    (h17930 : (¬ p101) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p346)) : (¬ p101) ∨ p344 ∨ (¬ p189) ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
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
    · exact False.elim (u1 q1)
  rcases h17930 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step31905 (p15 p21 p101 p344 p346 p495 : Prop)
    (h26863 : p346 ∨ p344)
    (h19695 : (¬ p15) ∨ (¬ p21) ∨ (¬ p101) ∨ (¬ p346) ∨ (¬ p495)) : (¬ p15) ∨ (¬ p101) ∨ (¬ p21) ∨ (¬ p495) ∨ p344 := by
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
  have u2 : p21 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19695 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)

theorem step31906 (p5 p6 p101 p344 p346 p595 p1286 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26863 : p346 ∨ p344)
    (h20641 : (¬ p5) ∨ (¬ p6) ∨ (¬ p101) ∨ (¬ p346) ∨ (¬ p595) ∨ (¬ p1286) ∨ (¬ p1333)) : (¬ p1286) ∨ p1325 ∨ (¬ p5) ∨ (¬ p101) ∨ p344 ∨ (¬ p6) ∨ (¬ p595) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20641 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u7)

theorem step31907 (p12 p344 p346 p980 p1036 p1083 p1452 : Prop)
    (h26907 : p1036 ∨ p12)
    (h26863 : p346 ∨ p344)
    (h20172 : (¬ p346) ∨ (¬ p980) ∨ (¬ p1036) ∨ (¬ p1083) ∨ (¬ p1452)) : (¬ p1083) ∨ (¬ p1452) ∨ (¬ p980) ∨ p12 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1083 := by
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
  have u3 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20172 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)

theorem step31908 (p344 p346 p662 p1076 : Prop)
    (h26863 : p346 ∨ p344)
    (h14136 : (¬ p346) ∨ (¬ p662) ∨ p1076) : p1076 ∨ p344 ∨ (¬ p662) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1076) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p662 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h14136 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (u0 q2)

theorem step31910 (p344 p346 p1074 p1076 p1077 p1096 p1099 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26913 : p1099 ∨ p1096)
    (h26863 : p346 ∨ p344)
    (h20244 : (¬ p346) ∨ (¬ p1074) ∨ (¬ p1077) ∨ (¬ p1099)) : p1076 ∨ p1096 ∨ (¬ p1074) ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1076) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20244 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step31911 (p12 p163 p167 p344 p346 p1036 p1076 p1077 : Prop)
    (h26863 : p346 ∨ p344)
    (h26907 : p1036 ∨ p12)
    (h26911 : p1077 ∨ p1076)
    (h26843 : p167 ∨ p163)
    (h20412 : (¬ p167) ∨ (¬ p346) ∨ (¬ p1036) ∨ (¬ p1077)) : p344 ∨ p12 ∨ p1076 ∨ p163 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p344) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p346 := by
    rcases h26863 with q0 | q1
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
  have u7 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20412 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)

theorem step31912 (p6 p41 p45 p101 p192 p344 p346 : Prop)
    (h26863 : p346 ∨ p344)
    (h26831 : p45 ∨ p41)
    (h18995 : (¬ p6) ∨ (¬ p45) ∨ (¬ p101) ∨ (¬ p192) ∨ (¬ p346)) : (¬ p101) ∨ p344 ∨ (¬ p192) ∨ (¬ p6) ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18995 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step31914 (p41 p45 p89 p124 p189 p193 p304 p344 p346 p576 p581 p734 : Prop)
    (h26845 : p193 ∨ p189)
    (h26879 : p581 ∨ p576)
    (h26831 : p45 ∨ p41)
    (h26859 : p304 ∨ p124)
    (h26863 : p346 ∨ p344)
    (h26135 : (¬ p581) ∨ (¬ p193) ∨ (¬ p734) ∨ (¬ p45) ∨ (¬ p304) ∨ (¬ p89) ∨ (¬ p346)) : p189 ∨ p576 ∨ (¬ p734) ∨ p41 ∨ p124 ∨ (¬ p89) ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p189) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h26135 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u11)

theorem step31915 (p41 p45 p89 p124 p189 p193 p304 p344 p346 p838 p1385 p1393 : Prop)
    (h26859 : p304 ∨ p124)
    (h26863 : p346 ∨ p344)
    (h26831 : p45 ∨ p41)
    (h26845 : p193 ∨ p189)
    (h26933 : p1393 ∨ p1385)
    (h26136 : (¬ p1393) ∨ (¬ p45) ∨ (¬ p304) ∨ (¬ p89) ∨ (¬ p346) ∨ (¬ p838) ∨ (¬ p193)) : (¬ p838) ∨ p124 ∨ p344 ∨ p41 ∨ p189 ∨ p1385 ∨ (¬ p89) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p838 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p89 := by
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
    · exact False.elim (u2 q1)
  have u9 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26136 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u11)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u10)

theorem step31916 (p41 p45 p89 p124 p189 p193 p224 p304 p344 p346 p576 p581 : Prop)
    (h26859 : p304 ∨ p124)
    (h26863 : p346 ∨ p344)
    (h26879 : p581 ∨ p576)
    (h26831 : p45 ∨ p41)
    (h26845 : p193 ∨ p189)
    (h26137 : (¬ p581) ∨ (¬ p193) ∨ (¬ p45) ∨ (¬ p304) ∨ (¬ p89) ∨ (¬ p346) ∨ (¬ p224)) : p124 ∨ p344 ∨ p576 ∨ (¬ p224) ∨ p41 ∨ (¬ p89) ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h26137 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u11)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u3)

theorem step31917 (p15 p305 p344 p346 p423 p756 p769 p1035 : Prop)
    (h26863 : p346 ∨ p344)
    (h26138 : (¬ p756) ∨ (¬ p305) ∨ (¬ p423) ∨ (¬ p1035) ∨ (¬ p15) ∨ (¬ p346) ∨ (¬ p769)) : (¬ p769) ∨ (¬ p756) ∨ (¬ p423) ∨ (¬ p1035) ∨ (¬ p15) ∨ p344 ∨ (¬ p305) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p769 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26138 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u0)

theorem step31918 (p88 p189 p193 p305 p344 p346 p422 p425 p582 p756 p769 p1035 p1256 : Prop)
    (h26863 : p346 ∨ p344)
    (h26929 : p1256 ∨ p422)
    (h26845 : p193 ∨ p189)
    (h16796 : p88 ∨ (¬ p193) ∨ (¬ p305) ∨ (¬ p346) ∨ (¬ p425) ∨ (¬ p582) ∨ (¬ p756) ∨ (¬ p769) ∨ (¬ p1035) ∨ (¬ p1256)) : (¬ p756) ∨ p344 ∨ (¬ p1035) ∨ p88 ∨ p422 ∨ (¬ p582) ∨ (¬ p769) ∨ p189 ∨ (¬ p425) ∨ (¬ p305) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p88) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p769 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u11 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u12 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h16796 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u12)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u2)
  · exact False.elim (q9 u11)

theorem step31919 (p84 p189 p193 p305 p344 p346 p419 p424 p425 p582 p996 p1055 p1076 p1077 : Prop)
    (h26905 : p996 ∨ p419)
    (h26863 : p346 ∨ p344)
    (h26911 : p1077 ∨ p1076)
    (h26845 : p193 ∨ p189)
    (h20285 : (¬ p84) ∨ (¬ p193) ∨ (¬ p305) ∨ (¬ p346) ∨ (¬ p424) ∨ (¬ p425) ∨ (¬ p582) ∨ (¬ p996) ∨ (¬ p1055) ∨ (¬ p1077)) : (¬ p1055) ∨ p419 ∨ (¬ p305) ∨ (¬ p84) ∨ p344 ∨ p1076 ∨ p189 ∨ (¬ p425) ∨ (¬ p582) ∨ (¬ p424) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p419) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u11 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u12 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u13 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20285 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u13)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u0)
  · exact False.elim (q9 u12)

theorem step31920 (p41 p45 p84 p135 p265 p305 p344 p346 p756 p769 p1035 p1255 p1346 : Prop)
    (h26863 : p346 ∨ p344)
    (h26831 : p45 ∨ p41)
    (h20079 : (¬ p45) ∨ (¬ p84) ∨ (¬ p135) ∨ (¬ p265) ∨ (¬ p305) ∨ (¬ p346) ∨ (¬ p756) ∨ (¬ p769) ∨ (¬ p1035) ∨ (¬ p1255) ∨ (¬ p1346)) : (¬ p305) ∨ (¬ p756) ∨ p344 ∨ (¬ p1255) ∨ (¬ p265) ∨ (¬ p135) ∨ (¬ p1035) ∨ p41 ∨ (¬ p769) ∨ (¬ p1346) ∨ (¬ p84) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1255 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p769 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u12 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h20079 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u12)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u3)
  · exact False.elim (q10 u9)

theorem step31922 (p10 p101 p124 p190 p211 p323 p382 p521 p789 p815 : Prop)
    (h26861 : p323 ∨ p10)
    (h19580 : (¬ p101) ∨ (¬ p124) ∨ (¬ p190) ∨ (¬ p211) ∨ (¬ p323) ∨ (¬ p382) ∨ (¬ p521) ∨ (¬ p789) ∨ (¬ p815)) : (¬ p521) ∨ (¬ p789) ∨ (¬ p101) ∨ p10 ∨ (¬ p124) ∨ (¬ p211) ∨ (¬ p815) ∨ (¬ p382) ∨ (¬ p190) := by
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
  have u2 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p815 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19580 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u6)

theorem step31923 (p124 p224 p344 p657 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26887 : p657 ∨ p224)
    (h19464 : (¬ p124) ∨ (¬ p344) ∨ (¬ p657) ∨ (¬ p1333)) : p1325 ∨ (¬ p344) ∨ (¬ p124) ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1325) := fun hu => hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19464 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step31924 (p41 p45 p101 p124 p262 p576 p581 : Prop)
    (h26831 : p45 ∨ p41)
    (h26879 : p581 ∨ p576)
    (h17786 : (¬ p45) ∨ (¬ p101) ∨ (¬ p124) ∨ (¬ p262) ∨ (¬ p581)) : (¬ p101) ∨ (¬ p124) ∨ (¬ p262) ∨ p41 ∨ p576 := by
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
  have u2 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17786 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)

theorem step31927 (p41 p45 p124 p192 p331 p382 p419 p420 p477 p498 p601 p633 p636 p996 : Prop)
    (h26885 : p636 ∨ p633)
    (h26831 : p45 ∨ p41)
    (h26881 : p601 ∨ p420)
    (h26905 : p996 ∨ p419)
    (h18281 : (¬ p45) ∨ (¬ p124) ∨ (¬ p192) ∨ (¬ p331) ∨ (¬ p382) ∨ (¬ p477) ∨ (¬ p498) ∨ (¬ p601) ∨ (¬ p636) ∨ (¬ p996)) : p633 ∨ (¬ p124) ∨ p41 ∨ (¬ p382) ∨ p420 ∨ (¬ p331) ∨ (¬ p192) ∨ (¬ p498) ∨ (¬ p477) ∨ p419 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p331 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p477 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u11 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u12 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u13 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h18281 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u11)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u12)
  · exact False.elim (q8 u10)
  · exact False.elim (q9 u13)

theorem step31929 (p124 p224 p262 p344 p576 p581 p657 : Prop)
    (h26879 : p581 ∨ p576)
    (h26887 : p657 ∨ p224)
    (h16256 : (¬ p124) ∨ (¬ p262) ∨ (¬ p344) ∨ (¬ p581) ∨ (¬ p657)) : (¬ p344) ∨ p576 ∨ p224 ∨ (¬ p124) ∨ (¬ p262) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16256 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)

theorem step31930 (p124 p262 p344 p576 p581 p1249 : Prop)
    (h26879 : p581 ∨ p576)
    (h17076 : (¬ p124) ∨ (¬ p262) ∨ (¬ p344) ∨ (¬ p581) ∨ (¬ p1249)) : (¬ p1249) ∨ p576 ∨ (¬ p262) ∨ (¬ p344) ∨ (¬ p124) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17076 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)

theorem step31931 (p124 p126 p258 p266 p331 p382 p419 p821 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h18960 : (¬ p124) ∨ (¬ p126) ∨ (¬ p258) ∨ (¬ p266) ∨ (¬ p331) ∨ (¬ p382) ∨ (¬ p821) ∨ (¬ p996)) : p419 ∨ (¬ p821) ∨ (¬ p382) ∨ (¬ p258) ∨ (¬ p266) ∨ (¬ p331) ∨ (¬ p124) ∨ (¬ p126) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : p821 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p382 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p331 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h18960 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u8)

theorem step31933 (p124 p268 p283 p1076 p1077 p1115 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h17239 : (¬ p124) ∨ (¬ p268) ∨ (¬ p283) ∨ (¬ p1077) ∨ (¬ p1115)) : p1076 ∨ (¬ p1115) ∨ (¬ p124) ∨ (¬ p268) ∨ (¬ p283) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1076) := fun hu => hn (Or.inl hu)
  have u1 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p268 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p283 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17239 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)

theorem step31934 (p124 p189 p224 p263 p344 p422 p657 p1004 : Prop)
    (h26887 : p657 ∨ p224)
    (h18177 : (¬ p124) ∨ (¬ p189) ∨ (¬ p263) ∨ (¬ p344) ∨ (¬ p422) ∨ (¬ p657) ∨ (¬ p1004)) : (¬ p422) ∨ (¬ p1004) ∨ (¬ p189) ∨ (¬ p344) ∨ p224 ∨ (¬ p263) ∨ (¬ p124) := by
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
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p263 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18177 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step31935 (p224 p382 p406 p656 p657 : Prop)
    (h26869 : p406 ∨ p382)
    (h26886 : (¬ p224) ∨ (¬ p657))
    (h12865 : (¬ p406) ∨ (¬ p656) ∨ p657) : p382 ∨ (¬ p656) ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p656 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : (¬ p657) := by
    rcases h26886 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h12865 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (u4 q2)

theorem step31937 (p63 p224 p789 p1385 p1393 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h18084 : (¬ p63) ∨ (¬ p224) ∨ (¬ p789) ∨ (¬ p1393)) : (¬ p789) ∨ p1385 ∨ (¬ p224) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1385) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
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
    · exact False.elim (u1 q1)
  rcases h18084 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)

theorem step31938 (p15 p224 p234 p419 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h20407 : (¬ p15) ∨ (¬ p224) ∨ (¬ p234) ∨ (¬ p996)) : p419 ∨ (¬ p15) ∨ (¬ p224) ∨ (¬ p234) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
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
  rcases h20407 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step31939 (p63 p224 p789 p839 p918 p928 : Prop)
    (h26901 : p928 ∨ p918)
    (h20526 : (¬ p63) ∨ (¬ p224) ∨ (¬ p789) ∨ (¬ p839) ∨ (¬ p928)) : (¬ p789) ∨ (¬ p224) ∨ (¬ p839) ∨ p918 ∨ (¬ p63) := by
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
  have u2 : p839 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20526 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step31940 (p3 p41 p45 p192 p224 p225 p226 : Prop)
    (h26847 : p226 ∨ p3)
    (h26831 : p45 ∨ p41)
    (h18533 : (¬ p45) ∨ (¬ p192) ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p226)) : p3 ∨ (¬ p192) ∨ (¬ p225) ∨ (¬ p224) ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18533 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step31941 (p163 p167 p189 p224 p225 : Prop)
    (h26843 : p167 ∨ p163)
    (h18536 : (¬ p167) ∨ (¬ p189) ∨ (¬ p224) ∨ (¬ p225)) : p163 ∨ (¬ p225) ∨ (¬ p189) ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p163) := fun hu => hn (Or.inl hu)
  have u1 : p225 := by
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
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h18536 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)

theorem step31942 (p185 p224 p303 p387 p836 : Prop)
    (h26867 : p387 ∨ p303)
    (h17951 : (¬ p185) ∨ (¬ p224) ∨ (¬ p387) ∨ (¬ p836)) : p303 ∨ (¬ p836) ∨ (¬ p224) ∨ (¬ p185) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17951 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)

theorem step31944 (p224 p225 p382 p406 p563 p680 : Prop)
    (h26869 : p406 ∨ p382)
    (h16200 : (¬ p224) ∨ (¬ p225) ∨ (¬ p406) ∨ (¬ p563) ∨ (¬ p680)) : p382 ∨ (¬ p563) ∨ (¬ p225) ∨ (¬ p224) ∨ (¬ p680) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p563 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
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
  rcases h16200 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)

theorem step31946 (p6 p121 p127 p185 p190 p224 p228 p836 : Prop)
    (h26839 : p127 ∨ p6)
    (h19015 : (¬ p121) ∨ (¬ p127) ∨ (¬ p185) ∨ (¬ p190) ∨ (¬ p224) ∨ (¬ p228) ∨ (¬ p836)) : (¬ p224) ∨ (¬ p836) ∨ (¬ p121) ∨ (¬ p185) ∨ p6 ∨ (¬ p228) ∨ (¬ p190) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19015 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u1)

theorem step31947 (p15 p124 p224 p304 p344 p346 p423 p1000 : Prop)
    (h26859 : p304 ∨ p124)
    (h26863 : p346 ∨ p344)
    (h26141 : (¬ p423) ∨ (¬ p304) ∨ (¬ p1000) ∨ (¬ p224) ∨ (¬ p15) ∨ (¬ p346)) : p124 ∨ p344 ∨ (¬ p15) ∨ (¬ p1000) ∨ (¬ p423) ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p224 := by
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
  rcases h26141 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)

theorem step31951 (p8 p18 p19 p44 p90 p101 p102 p189 p193 p224 p241 p710 p918 : Prop)
    (h26829 : p19 ∨ p18)
    (h26845 : p193 ∨ p189)
    (h26837 : p102 ∨ p101)
    (h26889 : p710 ∨ p8)
    (h26586 : p90)
    (h18663 : (¬ p19) ∨ (¬ p44) ∨ (¬ p90) ∨ (¬ p102) ∨ (¬ p193) ∨ (¬ p224) ∨ (¬ p241) ∨ (¬ p710) ∨ (¬ p918)) : p18 ∨ p189 ∨ p101 ∨ p8 ∨ (¬ p918) ∨ (¬ p224) ∨ (¬ p241) ∨ (¬ p44) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p18) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u12 : p90 := by
    exact h26586
  rcases h18663 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u12)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u11)
  · exact False.elim (q8 u4)

theorem step31952 (p166 p185 p189 p193 p224 p225 : Prop)
    (h26845 : p193 ∨ p189)
    (h19859 : (¬ p166) ∨ (¬ p185) ∨ (¬ p193) ∨ (¬ p224) ∨ (¬ p225)) : (¬ p166) ∨ p189 ∨ (¬ p185) ∨ (¬ p224) ∨ (¬ p225) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p166 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p185 := by
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
  have u5 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19859 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)

theorem step31955 (p8 p163 p167 p224 p560 p710 p1325 : Prop)
    (h26843 : p167 ∨ p163)
    (h26889 : p710 ∨ p8)
    (h18580 : (¬ p167) ∨ (¬ p224) ∨ (¬ p560) ∨ (¬ p710) ∨ (¬ p1325)) : p163 ∨ p8 ∨ (¬ p1325) ∨ (¬ p224) ∨ (¬ p560) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p163) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p8) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18580 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u2)

theorem step31956 (p224 p234 p480 p690 p728 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h19062 : (¬ p224) ∨ (¬ p480) ∨ (¬ p690) ∨ (¬ p728) ∨ (¬ p1187)) : (¬ p690) ∨ p234 ∨ (¬ p224) ∨ (¬ p480) ∨ (¬ p728) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p234) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p480 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19062 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)

theorem step31957 (p662 p836 p840 p1115 p1116 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h26894 : (¬ p836) ∨ (¬ p840))
    (h10623 : (¬ p662) ∨ p840 ∨ (¬ p1116)) : p1115 ∨ (¬ p836) ∨ (¬ p662) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1115) := fun hu => hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p662 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : (¬ p840) := by
    rcases h26894 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h10623 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u3)

theorem step31958 (p125 p126 p287 p301 p362 p1076 p1115 p1116 : Prop)
    (h26857 : p301 ∨ p126)
    (h26865 : p362 ∨ p125)
    (h26915 : p1116 ∨ p1115)
    (h17449 : (¬ p287) ∨ (¬ p301) ∨ (¬ p362) ∨ (¬ p1076) ∨ (¬ p1116)) : p126 ∨ p125 ∨ (¬ p287) ∨ p1115 ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p125) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17449 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u7)

theorem step31960 (p41 p125 p189 p224 p303 p657 p790 p838 : Prop)
    (h26887 : p657 ∨ p224)
    (h18791 : (¬ p41) ∨ (¬ p125) ∨ (¬ p189) ∨ (¬ p303) ∨ (¬ p657) ∨ (¬ p790) ∨ (¬ p838)) : (¬ p838) ∨ (¬ p125) ∨ p224 ∨ (¬ p790) ∨ (¬ p41) ∨ (¬ p303) ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p838 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p790 := by
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
  have u6 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18791 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u0)

theorem step31961 (p11 p17 p41 p189 p256 p1443 : Prop)
    (h26935 : p1443 ∨ p11)
    (h26853 : p256 ∨ p17)
    (h17115 : (¬ p41) ∨ (¬ p189) ∨ (¬ p256) ∨ (¬ p1443)) : p11 ∨ p17 ∨ (¬ p41) ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p11) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17115 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step31962 (p6 p10 p41 p127 p187 p303 p323 p387 : Prop)
    (h26867 : p387 ∨ p303)
    (h26839 : p127 ∨ p6)
    (h26861 : p323 ∨ p10)
    (h16268 : (¬ p41) ∨ (¬ p127) ∨ (¬ p187) ∨ (¬ p323) ∨ (¬ p387)) : p303 ∨ p6 ∨ (¬ p41) ∨ (¬ p187) ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16268 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u5)

theorem step31966 (p6 p41 p127 p187 p326 p798 p1385 : Prop)
    (h26839 : p127 ∨ p6)
    (h20192 : (¬ p41) ∨ (¬ p127) ∨ (¬ p187) ∨ (¬ p326) ∨ (¬ p798) ∨ (¬ p1385)) : p6 ∨ (¬ p798) ∨ (¬ p326) ∨ (¬ p1385) ∨ (¬ p187) ∨ (¬ p41) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p6) := fun hu => hn (Or.inl hu)
  have u1 : p798 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p326 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h20192 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u3)

theorem step31967 (p41 p189 p789 p858 p1385 : Prop)
    (h26897 : p858 ∨ p789)
    (h18911 : (¬ p41) ∨ (¬ p189) ∨ (¬ p858) ∨ (¬ p1385)) : (¬ p1385) ∨ (¬ p41) ∨ (¬ p189) ∨ p789 := by
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
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18911 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step31968 (p3 p5 p41 p89 p225 p226 p734 p790 p1385 : Prop)
    (h26847 : p226 ∨ p3)
    (h18319 : (¬ p5) ∨ (¬ p41) ∨ (¬ p89) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p734) ∨ (¬ p790) ∨ (¬ p1385)) : (¬ p1385) ∨ (¬ p790) ∨ (¬ p5) ∨ (¬ p225) ∨ (¬ p734) ∨ (¬ p89) ∨ (¬ p41) ∨ p3 := by
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
  have u2 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h18319 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u0)

theorem step31969 (p41 p189 p242 p1055 p1061 p1115 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h17535 : (¬ p41) ∨ (¬ p189) ∨ (¬ p242) ∨ (¬ p1061) ∨ (¬ p1115)) : (¬ p242) ∨ (¬ p1115) ∨ (¬ p41) ∨ (¬ p189) ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17535 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)

theorem step31970 (p41 p224 p657 p789 p858 p1385 : Prop)
    (h26887 : p657 ∨ p224)
    (h26897 : p858 ∨ p789)
    (h19748 : (¬ p41) ∨ (¬ p657) ∨ (¬ p858) ∨ (¬ p1385)) : p224 ∨ (¬ p1385) ∨ (¬ p41) ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p224) := fun hu => hn (Or.inl hu)
  have u1 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19748 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)

theorem step31971 (p41 p382 p406 p789 p858 p1385 : Prop)
    (h26869 : p406 ∨ p382)
    (h26897 : p858 ∨ p789)
    (h20602 : (¬ p41) ∨ (¬ p406) ∨ (¬ p858) ∨ (¬ p1385)) : p382 ∨ (¬ p1385) ∨ p789 ∨ (¬ p41) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20602 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)

theorem step31972 (p41 p101 p207 p227 p455 p456 p575 : Prop)
    (h26871 : p456 ∨ p455)
    (h18476 : (¬ p41) ∨ (¬ p101) ∨ (¬ p207) ∨ (¬ p227) ∨ (¬ p456) ∨ (¬ p575)) : p455 ∨ (¬ p101) ∨ (¬ p227) ∨ (¬ p41) ∨ (¬ p575) ∨ (¬ p207) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p575 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h18476 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u4)

theorem step31973 (p41 p101 p125 p207 p362 p420 p575 : Prop)
    (h26865 : p362 ∨ p125)
    (h18254 : (¬ p41) ∨ (¬ p101) ∨ (¬ p207) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p575)) : (¬ p420) ∨ (¬ p575) ∨ p125 ∨ (¬ p207) ∨ (¬ p41) ∨ (¬ p101) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p575 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18254 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u1)

theorem step31974 (p15 p69 p185 p234 p419 p860 p918 p928 p1187 p1346 : Prop)
    (h26901 : p928 ∨ p918)
    (h26921 : p1187 ∨ p234)
    (h26833 : p69 ∨ p15)
    (h18727 : (¬ p69) ∨ (¬ p185) ∨ (¬ p419) ∨ (¬ p860) ∨ (¬ p928) ∨ (¬ p1187) ∨ (¬ p1346)) : (¬ p1346) ∨ p918 ∨ p234 ∨ (¬ p419) ∨ p15 ∨ (¬ p860) ∨ (¬ p185) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p234) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p860 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18727 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u0)

theorem step31975 (p382 p406 p690 p918 p928 p1287 p1387 : Prop)
    (h26869 : p406 ∨ p382)
    (h26901 : p928 ∨ p918)
    (h17839 : (¬ p406) ∨ (¬ p690) ∨ (¬ p928) ∨ (¬ p1287) ∨ (¬ p1387)) : p382 ∨ p918 ∨ (¬ p690) ∨ (¬ p1387) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17839 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)

theorem step31976 (p728 p918 p928 p1015 p1385 : Prop)
    (h26901 : p928 ∨ p918)
    (h17224 : (¬ p728) ∨ (¬ p928) ∨ (¬ p1015) ∨ (¬ p1385)) : (¬ p1015) ∨ (¬ p728) ∨ (¬ p1385) ∨ p918 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17224 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u2)

theorem step31977 (p17 p135 p185 p256 p795 p862 p918 p928 p1249 : Prop)
    (h26901 : p928 ∨ p918)
    (h26853 : p256 ∨ p17)
    (h20186 : (¬ p135) ∨ (¬ p185) ∨ (¬ p256) ∨ (¬ p795) ∨ (¬ p862) ∨ (¬ p928) ∨ (¬ p1249)) : p918 ∨ (¬ p1249) ∨ (¬ p135) ∨ (¬ p862) ∨ (¬ p795) ∨ (¬ p185) ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p918) := fun hu => hn (Or.inl hu)
  have u1 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p862 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p795 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20186 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step31978 (p285 p344 p656 p819 p918 p928 p1385 : Prop)
    (h26901 : p928 ∨ p918)
    (h18678 : (¬ p285) ∨ (¬ p344) ∨ (¬ p656) ∨ (¬ p819) ∨ (¬ p928) ∨ (¬ p1385)) : (¬ p344) ∨ (¬ p819) ∨ (¬ p1385) ∨ p918 ∨ (¬ p285) ∨ (¬ p656) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p819 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p285 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p656 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18678 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)

theorem step31979 (p63 p224 p657 p836 p840 p918 p928 : Prop)
    (h26887 : p657 ∨ p224)
    (h26901 : p928 ∨ p918)
    (h26895 : p840 ∨ p836)
    (h18083 : (¬ p63) ∨ (¬ p657) ∨ (¬ p840) ∨ (¬ p928)) : p224 ∨ p918 ∨ p836 ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p224) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18083 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)

theorem step31981 (p2 p5 p63 p419 p918 p928 p1115 p1116 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h26901 : p928 ∨ p918)
    (h22543 : (¬ p63) ∨ (¬ p928) ∨ (¬ p2) ∨ (¬ p5) ∨ (¬ p419) ∨ (¬ p1116)) : (¬ p2) ∨ (¬ p63) ∨ (¬ p5) ∨ (¬ p419) ∨ p1115 ∨ p918 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u7 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h22543 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)

theorem step31982 (p12 p225 p544 p918 p928 p1036 p1115 p1116 : Prop)
    (h26877 : p544 ∨ p225)
    (h26907 : p1036 ∨ p12)
    (h26915 : p1116 ∨ p1115)
    (h26901 : p928 ∨ p918)
    (h17960 : (¬ p544) ∨ (¬ p928) ∨ (¬ p1036) ∨ (¬ p1116)) : p225 ∨ p12 ∨ p1115 ∨ p918 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p225) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  have u7 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17960 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)

theorem step31983 (p12 p168 p918 p928 p1118 p1249 : Prop)
    (h26901 : p928 ∨ p918)
    (h18287 : (¬ p12) ∨ (¬ p168) ∨ (¬ p928) ∨ (¬ p1118) ∨ (¬ p1249)) : (¬ p168) ∨ (¬ p1249) ∨ p918 ∨ (¬ p12) ∨ (¬ p1118) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p168 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1118 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18287 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u1)

theorem step31984 (p63 p422 p665 p918 p928 p1115 p1116 p1325 p1333 p1465 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26915 : p1116 ∨ p1115)
    (h26901 : p928 ∨ p918)
    (h18633 : (¬ p63) ∨ (¬ p422) ∨ (¬ p665) ∨ (¬ p928) ∨ (¬ p1116) ∨ (¬ p1333) ∨ (¬ p1465)) : p1325 ∨ (¬ p422) ∨ (¬ p1465) ∨ (¬ p63) ∨ p1115 ∨ p918 ∨ (¬ p665) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1325) := fun hu => hn (Or.inl hu)
  have u1 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18633 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u2)

theorem step31986 (p839 p918 p928 p1385 p1393 : Prop)
    (h26901 : p928 ∨ p918)
    (h26932 : (¬ p1385) ∨ (¬ p1393))
    (h13234 : (¬ p839) ∨ (¬ p928) ∨ p1393) : p918 ∨ (¬ p1385) ∨ (¬ p839) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p918) := fun hu => hn (Or.inl hu)
  have u1 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p839 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : (¬ p1393) := by
    rcases h26932 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h13234 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (u4 q2)

theorem step31987 (p41 p45 p89 p189 p193 p285 p918 p928 p1055 p1076 p1077 p1103 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26901 : p928 ∨ p918)
    (h26845 : p193 ∨ p189)
    (h26831 : p45 ∨ p41)
    (h20399 : (¬ p45) ∨ (¬ p89) ∨ (¬ p193) ∨ (¬ p285) ∨ (¬ p928) ∨ (¬ p1055) ∨ (¬ p1077) ∨ (¬ p1103)) : p1076 ∨ (¬ p1103) ∨ (¬ p285) ∨ (¬ p1055) ∨ (¬ p89) ∨ p918 ∨ p189 ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1076) := fun hu => hn (Or.inl hu)
  have u1 : p1103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p285 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h20399 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u11)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u1)

theorem step31989 (p83 p495 p499 p582 p790 p814 p839 p918 p928 : Prop)
    (h26901 : p928 ∨ p918)
    (h26875 : p499 ∨ p495)
    (h26893 : p814 ∨ p790)
    (h18379 : (¬ p83) ∨ (¬ p499) ∨ (¬ p582) ∨ (¬ p814) ∨ (¬ p839) ∨ (¬ p928)) : p918 ∨ p495 ∨ (¬ p83) ∨ (¬ p582) ∨ (¬ p839) ∨ p790 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p918) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p839 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18379 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)

theorem step31990 (p303 p521 p790 p814 p1346 : Prop)
    (h26893 : p814 ∨ p790)
    (h23746 : (¬ p1346) ∨ (¬ p521) ∨ (¬ p303) ∨ (¬ p814)) : (¬ p1346) ∨ p790 ∨ (¬ p303) ∨ (¬ p521) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p790) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p521 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h23746 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step31991 (p185 p237 p790 p814 p839 : Prop)
    (h26893 : p814 ∨ p790)
    (h26851 : p237 ∨ p185)
    (h5327 : (¬ p237) ∨ (¬ p814) ∨ (¬ p839)) : p790 ∨ p185 ∨ (¬ p839) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p790) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p839 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h5327 with q0 | q1 | q2
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)

theorem step31992 (p185 p237 p789 p790 p814 p858 p918 : Prop)
    (h26893 : p814 ∨ p790)
    (h26851 : p237 ∨ p185)
    (h26897 : p858 ∨ p789)
    (h20331 : (¬ p237) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p918)) : p790 ∨ p185 ∨ (¬ p918) ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p790) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20331 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)

theorem step31993 (p17 p256 p789 p790 p814 p858 p1325 : Prop)
    (h26893 : p814 ∨ p790)
    (h26853 : p256 ∨ p17)
    (h26897 : p858 ∨ p789)
    (h19213 : (¬ p256) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1325)) : p790 ∨ p17 ∨ (¬ p1325) ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p790) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19213 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)

theorem step31994 (p17 p256 p303 p387 p789 p790 p814 p858 : Prop)
    (h26867 : p387 ∨ p303)
    (h26893 : p814 ∨ p790)
    (h26853 : p256 ∨ p17)
    (h26897 : p858 ∨ p789)
    (h19349 : (¬ p256) ∨ (¬ p387) ∨ (¬ p814) ∨ (¬ p858)) : p303 ∨ p790 ∨ p17 ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p790) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19349 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u7)

theorem step31996 (p189 p193 p790 p795 p814 : Prop)
    (h26893 : p814 ∨ p790)
    (h26845 : p193 ∨ p189)
    (h4668 : (¬ p193) ∨ (¬ p795) ∨ (¬ p814)) : p790 ∨ p189 ∨ (¬ p795) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p790) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p795 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h4668 with q0 | q1 | q2
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)

theorem step31997 (p189 p193 p434 p790 p814 p1015 : Prop)
    (h26845 : p193 ∨ p189)
    (h26893 : p814 ∨ p790)
    (h16598 : (¬ p193) ∨ (¬ p434) ∨ (¬ p814) ∨ (¬ p1015)) : (¬ p1015) ∨ (¬ p434) ∨ p189 ∨ p790 := by
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
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16598 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)

theorem step31999 (p189 p193 p790 p814 p1015 p1366 : Prop)
    (h26893 : p814 ∨ p790)
    (h26845 : p193 ∨ p189)
    (h17597 : (¬ p193) ∨ (¬ p814) ∨ (¬ p1015) ∨ (¬ p1366)) : p790 ∨ (¬ p1015) ∨ p189 ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p790) := fun hu => hn (Or.inl hu)
  have u1 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17597 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)

theorem step32000 (p17 p41 p45 p256 p790 p814 p1385 p1393 : Prop)
    (h26893 : p814 ∨ p790)
    (h26853 : p256 ∨ p17)
    (h26933 : p1393 ∨ p1385)
    (h26831 : p45 ∨ p41)
    (h17396 : (¬ p45) ∨ (¬ p256) ∨ (¬ p814) ∨ (¬ p1393)) : p790 ∨ p17 ∨ p1385 ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p790) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17396 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)

theorem step32001 (p41 p45 p789 p790 p814 p858 p1286 p1392 : Prop)
    (h26897 : p858 ∨ p789)
    (h26893 : p814 ∨ p790)
    (h26831 : p45 ∨ p41)
    (h19024 : (¬ p45) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1286) ∨ (¬ p1392)) : (¬ p1392) ∨ (¬ p1286) ∨ p789 ∨ p790 ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1392 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19024 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)

theorem step32003 (p88 p790 p814 p1385 p1393 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h26893 : p814 ∨ p790)
    (h12086 : (¬ p88) ∨ (¬ p814) ∨ (¬ p1393)) : p1385 ∨ p790 ∨ (¬ p88) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1385) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p790) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h12086 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)

theorem step32004 (p6 p39 p68 p88 p121 p127 p790 p814 p1015 p1335 p1452 : Prop)
    (h26839 : p127 ∨ p6)
    (h26893 : p814 ∨ p790)
    (h17608 : (¬ p39) ∨ (¬ p68) ∨ (¬ p88) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p814) ∨ (¬ p1015) ∨ (¬ p1335) ∨ (¬ p1452)) : (¬ p88) ∨ (¬ p1452) ∨ (¬ p121) ∨ (¬ p68) ∨ p6 ∨ p790 ∨ (¬ p1015) ∨ (¬ p1335) ∨ (¬ p39) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17608 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u1)

theorem step32005 (p101 p102 p124 p125 p304 p331 p362 p419 p789 p790 p814 p858 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h26859 : p304 ∨ p124)
    (h26865 : p362 ∨ p125)
    (h26837 : p102 ∨ p101)
    (h26897 : p858 ∨ p789)
    (h26893 : p814 ∨ p790)
    (h18511 : (¬ p102) ∨ (¬ p304) ∨ (¬ p331) ∨ (¬ p362) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p996)) : p419 ∨ p124 ∨ (¬ p331) ∨ p125 ∨ p101 ∨ p789 ∨ p790 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p331 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u12 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18511 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u12)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u7)

theorem step32006 (p17 p101 p102 p140 p256 p515 p790 p814 : Prop)
    (h26893 : p814 ∨ p790)
    (h26837 : p102 ∨ p101)
    (h26853 : p256 ∨ p17)
    (h24215 : (¬ p140) ∨ (¬ p515) ∨ (¬ p256) ∨ (¬ p102) ∨ (¬ p814)) : (¬ p515) ∨ p790 ∨ p101 ∨ (¬ p140) ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p515 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p790) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h24215 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step32007 (p126 p301 p518 : Prop)
    (h26856 : (¬ p126) ∨ (¬ p301))
    (h20992 : p301 ∨ p518) : (¬ p126) ∨ p518 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p518) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p301) := by
    rcases h26856 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h20992 with q0 | q1
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)

theorem step32008 (p126 p301 p520 : Prop)
    (h26856 : (¬ p126) ∨ (¬ p301))
    (h21270 : p520 ∨ p301) : p520 ∨ (¬ p126) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p520) := fun hu => hn (Or.inl hu)
  have u1 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p301) := by
    rcases h26856 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h21270 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step32011 (p3 p194 p226 p789 p790 p940 p985 p1325 p1333 : Prop)
    (h26847 : p226 ∨ p3)
    (h26931 : p1333 ∨ p1325)
    (h16449 : (¬ p194) ∨ (¬ p226) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1333)) : (¬ p940) ∨ (¬ p194) ∨ p3 ∨ p1325 ∨ (¬ p790) ∨ (¬ p789) ∨ (¬ p985) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16449 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u8)

theorem step32012 (p3 p194 p225 p226 p734 p1335 p1346 p1508 : Prop)
    (h26847 : p226 ∨ p3)
    (h18900 : (¬ p194) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p734) ∨ (¬ p1335) ∨ (¬ p1346) ∨ (¬ p1508)) : p3 ∨ (¬ p225) ∨ (¬ p194) ∨ (¬ p734) ∨ (¬ p1508) ∨ (¬ p1346) ∨ (¬ p1335) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h18900 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u4)

theorem step32014 (p3 p11 p12 p125 p126 p194 p226 p266 p301 p362 p1036 p1081 p1443 : Prop)
    (h26847 : p226 ∨ p3)
    (h26857 : p301 ∨ p126)
    (h26865 : p362 ∨ p125)
    (h26935 : p1443 ∨ p11)
    (h26907 : p1036 ∨ p12)
    (h16683 : (¬ p194) ∨ (¬ p226) ∨ (¬ p266) ∨ (¬ p301) ∨ (¬ p362) ∨ (¬ p1036) ∨ (¬ p1081) ∨ (¬ p1443)) : p3 ∨ p126 ∨ p125 ∨ (¬ p266) ∨ p11 ∨ p12 ∨ (¬ p1081) ∨ (¬ p194) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u12 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h16683 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u12)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u11)

theorem step32016 (p12 p17 p126 p194 p225 p256 p303 p387 p556 p1055 : Prop)
    (h26867 : p387 ∨ p303)
    (h26853 : p256 ∨ p17)
    (h19491 : (¬ p12) ∨ (¬ p126) ∨ (¬ p194) ∨ (¬ p225) ∨ (¬ p256) ∨ (¬ p387) ∨ (¬ p556) ∨ (¬ p1055)) : (¬ p556) ∨ p303 ∨ p17 ∨ (¬ p194) ∨ (¬ p1055) ∨ (¬ p12) ∨ (¬ p126) ∨ (¬ p225) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p556 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19491 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u4)

theorem step32018 (p189 p190 p193 p196 p197 p198 p199 p200 : Prop)
    (h26844 : (¬ p189) ∨ (¬ p193))
    (h939 : p190 ∨ p193 ∨ (¬ p196) ∨ (¬ p197) ∨ (¬ p198) ∨ (¬ p199) ∨ (¬ p200)) : (¬ p198) ∨ (¬ p196) ∨ (¬ p189) ∨ p190 ∨ (¬ p197) ∨ (¬ p199) ∨ (¬ p200) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p198 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p196 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p190) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p197 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p199 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p200 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p193) := by
    rcases h26844 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h939 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)

theorem step32020 (p431 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h20130 : p431 ∨ (¬ p1333)) : p431 ∨ p1325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p431) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr hu)
  have u2 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20130 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)

theorem step32021 (p124 p532 p961 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h18659 : (¬ p124) ∨ (¬ p532) ∨ (¬ p961) ∨ (¬ p1333)) : (¬ p532) ∨ p1325 ∨ (¬ p124) ∨ (¬ p961) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18659 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step32023 (p383 p532 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h13102 : (¬ p383) ∨ (¬ p532) ∨ (¬ p1333)) : (¬ p383) ∨ p1325 ∨ (¬ p532) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p383 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h13102 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)

theorem step32024 (p3 p41 p45 p125 p192 p226 p303 p362 p387 p940 p985 p1325 p1333 : Prop)
    (h26867 : p387 ∨ p303)
    (h26847 : p226 ∨ p3)
    (h26865 : p362 ∨ p125)
    (h26931 : p1333 ∨ p1325)
    (h26831 : p45 ∨ p41)
    (h19454 : (¬ p45) ∨ (¬ p192) ∨ (¬ p226) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1333)) : (¬ p940) ∨ p303 ∨ p3 ∨ p125 ∨ (¬ p985) ∨ (¬ p192) ∨ p1325 ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u12 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h19454 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u12)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u11)

theorem step32025 (p134 p210 p532 p961 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h18611 : (¬ p134) ∨ (¬ p210) ∨ (¬ p532) ∨ (¬ p961) ∨ (¬ p1333)) : (¬ p961) ∨ (¬ p210) ∨ p1325 ∨ (¬ p532) ∨ (¬ p134) := by
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
  have u2 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18611 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)

theorem step32026 (p381 p521 p532 p789 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h17651 : (¬ p381) ∨ (¬ p521) ∨ (¬ p532) ∨ (¬ p789) ∨ (¬ p1333)) : (¬ p521) ∨ (¬ p789) ∨ p1325 ∨ (¬ p381) ∨ (¬ p532) := by
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
  have u2 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p381 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17651 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)

theorem step32027 (p224 p347 p381 p532 p657 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26887 : p657 ∨ p224)
    (h18865 : (¬ p347) ∨ (¬ p381) ∨ (¬ p532) ∨ (¬ p657) ∨ (¬ p1333)) : p1325 ∨ (¬ p347) ∨ p224 ∨ (¬ p532) ∨ (¬ p381) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1325) := fun hu => hn (Or.inl hu)
  have u1 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p381 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18865 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step32029 (p86 p344 p346 p495 p633 p636 p789 p790 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26885 : p636 ∨ p633)
    (h26863 : p346 ∨ p344)
    (h20248 : (¬ p86) ∨ (¬ p346) ∨ (¬ p495) ∨ (¬ p636) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1333)) : p1325 ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p86) ∨ p633 ∨ p344 ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1325) := fun hu => hn (Or.inl hu)
  have u1 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p633) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20248 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u7)

theorem step32030 (p224 p542 p657 p997 p1325 p1333 p1465 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26887 : p657 ∨ p224)
    (h16797 : (¬ p542) ∨ (¬ p657) ∨ (¬ p997) ∨ (¬ p1333) ∨ (¬ p1465)) : p1325 ∨ p224 ∨ (¬ p1465) ∨ (¬ p542) ∨ (¬ p997) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1325) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p997 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16797 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)

theorem step32031 (p303 p381 p387 : Prop)
    (h26866 : (¬ p303) ∨ (¬ p387))
    (h20914 : p387 ∨ p381) : (¬ p303) ∨ p381 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p381) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p387) := by
    rcases h26866 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h20914 with q0 | q1
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)

theorem step32034 (p228 p303 p387 : Prop)
    (h26866 : (¬ p303) ∨ (¬ p387))
    (h21214 : p228 ∨ p387) : p228 ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p228) := fun hu => hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p387) := by
    rcases h26866 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h21214 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step32035 (p980 p983 p1330 : Prop)
    (h26903 : p983 ∨ p980)
    (h16755 : (¬ p983) ∨ p1330) : p980 ∨ p1330 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1330) := fun hu => hn (Or.inr hu)
  have u2 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h16755 with q0 | q1
  · exact False.elim (q0 u2)
  · exact False.elim (u1 q1)

theorem step32040 (p11 p258 p1078 p1443 : Prop)
    (h26935 : p1443 ∨ p11)
    (h13111 : (¬ p258) ∨ (¬ p1078) ∨ (¬ p1443)) : (¬ p258) ∨ (¬ p1078) ∨ p11 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1078 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p11) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h13111 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)

theorem step32041 (p312 p532 p980 p983 p1055 p1061 p1078 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h26903 : p983 ∨ p980)
    (h17629 : (¬ p312) ∨ (¬ p532) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1078)) : p1055 ∨ p980 ∨ (¬ p532) ∨ (¬ p312) ∨ (¬ p1078) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1055) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p312 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1078 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17629 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)

theorem step32044 (p101 p102 p106 : Prop)
    (h26837 : p102 ∨ p101)
    (h16196 : (¬ p102) ∨ p106) : p101 ∨ p106 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p101) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p106) := fun hu => hn (Or.inr hu)
  have u2 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h16196 with q0 | q1
  · exact False.elim (q0 u2)
  · exact False.elim (u1 q1)

theorem step32045 (p101 p102 p125 p140 p189 p265 p419 p431 p438 p790 p801 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h26837 : p102 ∨ p101)
    (h20428 : (¬ p102) ∨ (¬ p125) ∨ (¬ p140) ∨ (¬ p189) ∨ (¬ p265) ∨ (¬ p431) ∨ (¬ p438) ∨ (¬ p790) ∨ (¬ p801) ∨ (¬ p996)) : p419 ∨ (¬ p431) ∨ (¬ p801) ∨ p101 ∨ (¬ p438) ∨ (¬ p189) ∨ (¬ p140) ∨ (¬ p125) ∨ (¬ p790) ∨ (¬ p265) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p801 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u11 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20428 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u11)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u2)
  · exact False.elim (q9 u10)

theorem step32046 (p6 p101 p102 p127 p190 p344 p382 p789 p815 p842 : Prop)
    (h26839 : p127 ∨ p6)
    (h26837 : p102 ∨ p101)
    (h19239 : (¬ p102) ∨ (¬ p127) ∨ (¬ p190) ∨ (¬ p344) ∨ (¬ p382) ∨ (¬ p789) ∨ (¬ p815) ∨ (¬ p842)) : (¬ p789) ∨ (¬ p344) ∨ p6 ∨ (¬ p382) ∨ (¬ p190) ∨ (¬ p815) ∨ (¬ p842) ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p815 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p842 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h19239 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step32047 (p41 p101 p102 p187 p211 p1631 p1666 : Prop)
    (h26837 : p102 ∨ p101)
    (h17135 : (¬ p41) ∨ (¬ p102) ∨ (¬ p187) ∨ (¬ p211) ∨ (¬ p1631) ∨ (¬ p1666)) : (¬ p1631) ∨ (¬ p211) ∨ (¬ p1666) ∨ p101 ∨ (¬ p41) ∨ (¬ p187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1631 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1666 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17135 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u2)

theorem step32048 (p6 p101 p102 p127 p185 p190 p668 p836 p1076 p1077 : Prop)
    (h26839 : p127 ∨ p6)
    (h26837 : p102 ∨ p101)
    (h26911 : p1077 ∨ p1076)
    (h19083 : (¬ p102) ∨ (¬ p127) ∨ (¬ p185) ∨ (¬ p190) ∨ (¬ p668) ∨ (¬ p836) ∨ (¬ p1077)) : (¬ p836) ∨ (¬ p185) ∨ p6 ∨ (¬ p668) ∨ p101 ∨ p1076 ∨ (¬ p190) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19083 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u9)

theorem step32049 (p101 p102 p140 p258 : Prop)
    (h26837 : p102 ∨ p101)
    (h1445 : (¬ p102) ∨ (¬ p140) ∨ (¬ p258)) : p101 ∨ (¬ p258) ∨ (¬ p140) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p101) := fun hu => hn (Or.inl hu)
  have u1 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1445 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)

theorem step32051 (p6 p41 p101 p102 p127 p187 p344 : Prop)
    (h26839 : p127 ∨ p6)
    (h26837 : p102 ∨ p101)
    (h16274 : (¬ p41) ∨ (¬ p102) ∨ (¬ p127) ∨ (¬ p187) ∨ (¬ p344)) : p6 ∨ (¬ p344) ∨ (¬ p41) ∨ (¬ p187) ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p6) := fun hu => hn (Or.inl hu)
  have u1 : p344 := by
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
  have u4 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16274 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)

theorem step32052 (p6 p41 p101 p102 p127 p187 p1249 : Prop)
    (h26839 : p127 ∨ p6)
    (h26837 : p102 ∨ p101)
    (h17138 : (¬ p41) ∨ (¬ p102) ∨ (¬ p127) ∨ (¬ p187) ∨ (¬ p1249)) : (¬ p1249) ∨ p6 ∨ p101 ∨ (¬ p41) ∨ (¬ p187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17138 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u0)

theorem step32053 (p6 p41 p101 p102 p127 p187 p1076 p1077 : Prop)
    (h26839 : p127 ∨ p6)
    (h26911 : p1077 ∨ p1076)
    (h26837 : p102 ∨ p101)
    (h17441 : (¬ p41) ∨ (¬ p102) ∨ (¬ p127) ∨ (¬ p187) ∨ (¬ p1077)) : p6 ∨ p1076 ∨ p101 ∨ (¬ p41) ∨ (¬ p187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p6) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17441 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u6)

theorem step32054 (p41 p45 p63 p85 p101 p102 p136 p258 : Prop)
    (h26831 : p45 ∨ p41)
    (h26837 : p102 ∨ p101)
    (h26835 : p85 ∨ p63)
    (h16852 : (¬ p45) ∨ (¬ p85) ∨ (¬ p102) ∨ (¬ p136) ∨ (¬ p258)) : (¬ p258) ∨ p41 ∨ (¬ p136) ∨ p101 ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p41) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p136 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16852 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u0)

theorem step32055 (p6 p101 p102 p127 p224 p344 p657 : Prop)
    (h26887 : p657 ∨ p224)
    (h26839 : p127 ∨ p6)
    (h26837 : p102 ∨ p101)
    (h17842 : (¬ p102) ∨ (¬ p127) ∨ (¬ p344) ∨ (¬ p657)) : p224 ∨ p6 ∨ p101 ∨ (¬ p344) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p224) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17842 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step32057 (p101 p102 p124 p140 p265 p304 : Prop)
    (h26859 : p304 ∨ p124)
    (h26837 : p102 ∨ p101)
    (h13827 : (¬ p102) ∨ (¬ p140) ∨ (¬ p265) ∨ (¬ p304)) : p124 ∨ (¬ p265) ∨ (¬ p140) ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h13827 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)

theorem step32058 (p101 p102 p121 p124 p304 p532 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26859 : p304 ∨ p124)
    (h26837 : p102 ∨ p101)
    (h16525 : (¬ p102) ∨ (¬ p304) ∨ (¬ p532) ∨ (¬ p1206)) : p121 ∨ p124 ∨ (¬ p532) ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16525 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step32060 (p6 p101 p102 p127 p190 p665 p789 p790 p814 p858 p1076 p1077 : Prop)
    (h26893 : p814 ∨ p790)
    (h26839 : p127 ∨ p6)
    (h26837 : p102 ∨ p101)
    (h26897 : p858 ∨ p789)
    (h26911 : p1077 ∨ p1076)
    (h19238 : (¬ p102) ∨ (¬ p127) ∨ (¬ p190) ∨ (¬ p665) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1077)) : p790 ∨ p6 ∨ (¬ p190) ∨ p101 ∨ (¬ p665) ∨ p789 ∨ p1076 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p790) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u11 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19238 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step32061 (p8 p101 p102 p209 p305 p344 p710 : Prop)
    (h26837 : p102 ∨ p101)
    (h26889 : p710 ∨ p8)
    (h16356 : (¬ p102) ∨ (¬ p209) ∨ (¬ p305) ∨ (¬ p344) ∨ (¬ p710)) : (¬ p305) ∨ (¬ p344) ∨ p101 ∨ p8 ∨ (¬ p209) := by
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
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16356 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)

theorem step32063 (p2 p41 p45 p191 p801 p1385 p1393 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h26831 : p45 ∨ p41)
    (h19877 : (¬ p2) ∨ (¬ p45) ∨ (¬ p191) ∨ (¬ p801) ∨ (¬ p1393)) : (¬ p2) ∨ p1385 ∨ (¬ p191) ∨ (¬ p801) ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1385) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p801 := by
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
  rcases h19877 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)

theorem step32064 (p121 p134 p189 p532 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h19777 : (¬ p134) ∨ (¬ p189) ∨ (¬ p532) ∨ (¬ p1206)) : p121 ∨ (¬ p189) ∨ (¬ p532) ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
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
  rcases h19777 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step32065 (p455 p456 p495 p532 p980 p983 : Prop)
    (h26871 : p456 ∨ p455)
    (h26903 : p983 ∨ p980)
    (h17055 : (¬ p456) ∨ (¬ p495) ∨ (¬ p532) ∨ (¬ p983)) : p455 ∨ p980 ∨ (¬ p532) ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
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
  have u5 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17055 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)

theorem step32066 (p455 p456 p495 p532 p1325 p1333 : Prop)
    (h26871 : p456 ∨ p455)
    (h26931 : p1333 ∨ p1325)
    (h18711 : (¬ p456) ∨ (¬ p495) ∨ (¬ p532) ∨ (¬ p1333)) : p455 ∨ p1325 ∨ (¬ p532) ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
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
  have u5 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18711 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)

theorem step32067 (p185 p237 p267 p532 p728 p836 p840 p961 p1330 : Prop)
    (h26851 : p237 ∨ p185)
    (h26895 : p840 ∨ p836)
    (h20275 : (¬ p237) ∨ (¬ p267) ∨ (¬ p532) ∨ (¬ p728) ∨ (¬ p840) ∨ (¬ p961) ∨ (¬ p1330)) : (¬ p728) ∨ p185 ∨ (¬ p961) ∨ p836 ∨ (¬ p532) ∨ (¬ p1330) ∨ (¬ p267) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p267 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20275 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u5)

theorem step32068 (p39 p63 p68 p595 p616 p1035 p1140 p1335 p1545 : Prop)
    (h26883 : p616 ∨ p595)
    (h19357 : (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p616) ∨ (¬ p1035) ∨ (¬ p1140) ∨ (¬ p1335) ∨ (¬ p1545)) : (¬ p1035) ∨ (¬ p68) ∨ (¬ p1140) ∨ (¬ p63) ∨ (¬ p1545) ∨ (¬ p39) ∨ p595 ∨ (¬ p1335) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19357 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step32069 (p63 p85 p1015 p1035 p1140 p1335 p1385 : Prop)
    (h26835 : p85 ∨ p63)
    (h26143 : (¬ p1015) ∨ (¬ p1385) ∨ (¬ p1335) ∨ (¬ p85) ∨ (¬ p1035) ∨ (¬ p1140)) : (¬ p1035) ∨ (¬ p1140) ∨ (¬ p1015) ∨ (¬ p1385) ∨ p63 ∨ (¬ p1335) := by
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
  have u2 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h26143 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u1)

theorem step32070 (p124 p190 p261 p304 p344 p346 p734 p1035 p1140 p1335 : Prop)
    (h26859 : p304 ∨ p124)
    (h26863 : p346 ∨ p344)
    (h20106 : (¬ p190) ∨ (¬ p261) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p734) ∨ (¬ p1035) ∨ (¬ p1140) ∨ (¬ p1335)) : p124 ∨ (¬ p1140) ∨ (¬ p190) ∨ p344 ∨ (¬ p1035) ∨ (¬ p734) ∨ (¬ p261) ∨ (¬ p1335) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1335 := by
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
    · exact False.elim (u3 q1)
  rcases h20106 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u7)

theorem step32072 (p134 p422 p532 p1035 p1256 : Prop)
    (h26929 : p1256 ∨ p422)
    (h19970 : (¬ p134) ∨ (¬ p532) ∨ (¬ p1035) ∨ (¬ p1256)) : p422 ∨ (¬ p1035) ∨ (¬ p134) ∨ (¬ p532) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p422) := fun hu => hn (Or.inl hu)
  have u1 : p1035 := by
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
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19970 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)

theorem step32073 (p134 p422 p980 p1035 p1256 : Prop)
    (h26929 : p1256 ∨ p422)
    (h19425 : (¬ p134) ∨ (¬ p980) ∨ (¬ p1035) ∨ (¬ p1256)) : (¬ p1035) ∨ p422 ∨ (¬ p980) ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p422) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19425 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)

theorem step32074 (p3 p67 p226 p423 p883 p1035 p1074 p1325 : Prop)
    (h26847 : p226 ∨ p3)
    (h26144 : (¬ p1035) ∨ (¬ p1325) ∨ (¬ p67) ∨ (¬ p423) ∨ (¬ p226) ∨ (¬ p883) ∨ (¬ p1074)) : (¬ p1035) ∨ (¬ p1074) ∨ (¬ p67) ∨ (¬ p1325) ∨ (¬ p883) ∨ (¬ p423) ∨ p3 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p883 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h26144 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u1)

theorem step32075 (p86 p189 p193 p422 p595 p616 p1035 p1256 p1335 p1545 : Prop)
    (h26929 : p1256 ∨ p422)
    (h26845 : p193 ∨ p189)
    (h26883 : p616 ∨ p595)
    (h18778 : (¬ p86) ∨ (¬ p193) ∨ (¬ p616) ∨ (¬ p1035) ∨ (¬ p1256) ∨ (¬ p1335) ∨ (¬ p1545)) : p422 ∨ p189 ∨ (¬ p86) ∨ (¬ p1545) ∨ (¬ p1335) ∨ (¬ p1035) ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p422) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18778 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u3)

theorem step32076 (p124 p189 p193 p267 p304 p422 p726 p985 p1035 p1256 : Prop)
    (h26859 : p304 ∨ p124)
    (h26845 : p193 ∨ p189)
    (h26929 : p1256 ∨ p422)
    (h17694 : (¬ p193) ∨ (¬ p267) ∨ (¬ p304) ∨ (¬ p726) ∨ (¬ p985) ∨ (¬ p1035) ∨ (¬ p1256)) : (¬ p726) ∨ p124 ∨ (¬ p985) ∨ (¬ p267) ∨ p189 ∨ (¬ p1035) ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p267 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h17694 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u9)

theorem step32077 (p15 p124 p304 p423 p726 p985 p1035 : Prop)
    (h26859 : p304 ∨ p124)
    (h26145 : (¬ p985) ∨ (¬ p726) ∨ (¬ p423) ∨ (¬ p1035) ∨ (¬ p304) ∨ (¬ p15)) : (¬ p1035) ∨ p124 ∨ (¬ p423) ∨ (¬ p726) ∨ (¬ p985) ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p423 := by
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
  have u5 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h26145 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u5)

theorem step32078 (p495 p633 p636 p726 p985 p1035 p1140 : Prop)
    (h26885 : p636 ∨ p633)
    (h26146 : (¬ p1035) ∨ (¬ p985) ∨ (¬ p495) ∨ (¬ p1140) ∨ (¬ p726) ∨ (¬ p636)) : (¬ p1035) ∨ (¬ p726) ∨ (¬ p1140) ∨ p633 ∨ (¬ p495) ∨ (¬ p985) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p633) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h26146 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u6)

theorem step32079 (p121 p125 p207 p362 p386 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26865 : p362 ∨ p125)
    (h14820 : (¬ p207) ∨ (¬ p362) ∨ (¬ p386) ∨ (¬ p1206)) : (¬ p386) ∨ p121 ∨ p125 ∨ (¬ p207) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p386 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p121) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h14820 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)

theorem step32085 (p14 p423 p1141 p1325 p1333 p1465 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26931 : p1333 ∨ p1325)
    (h16551 : (¬ p14) ∨ (¬ p1141) ∨ (¬ p1333) ∨ (¬ p1465)) : p423 ∨ p1325 ∨ (¬ p14) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p14 := by
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
  rcases h16551 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)

theorem step32086 (p47 p422 p423 p1141 p1256 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26929 : p1256 ∨ p422)
    (h11340 : (¬ p47) ∨ (¬ p1141) ∨ (¬ p1256)) : p423 ∨ (¬ p47) ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p422) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h11340 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)

theorem step32088 (p14 p163 p167 p423 p1141 p1465 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26843 : p167 ∨ p163)
    (h17943 : (¬ p14) ∨ (¬ p167) ∨ (¬ p1141) ∨ (¬ p1465)) : p423 ∨ (¬ p14) ∨ (¬ p1465) ∨ p163 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17943 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)

theorem step32090 (p14 p423 p563 p1038 p1055 p1061 p1141 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26909 : p1061 ∨ p1055)
    (h18638 : (¬ p14) ∨ (¬ p563) ∨ (¬ p1038) ∨ (¬ p1061) ∨ (¬ p1141)) : p423 ∨ p1055 ∨ (¬ p1038) ∨ (¬ p563) ∨ (¬ p14) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1038 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p563 := by
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
  have u6 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18638 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step32091 (p14 p423 p790 p814 p1141 p1255 p1346 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26893 : p814 ∨ p790)
    (h20422 : (¬ p14) ∨ (¬ p814) ∨ (¬ p1141) ∨ (¬ p1255) ∨ (¬ p1346)) : p423 ∨ (¬ p1346) ∨ (¬ p14) ∨ p790 ∨ (¬ p1255) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1255 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20422 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u1)

theorem step32092 (p6 p14 p109 p423 p1140 p1141 : Prop)
    (h26917 : p1141 ∨ p423)
    (h19399 : (¬ p6) ∨ (¬ p14) ∨ (¬ p109) ∨ (¬ p1140) ∨ (¬ p1141)) : p423 ∨ (¬ p1140) ∨ (¬ p109) ∨ (¬ p14) ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p109 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19399 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)

theorem step32093 (p14 p106 p423 p1038 p1076 p1077 p1141 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26911 : p1077 ∨ p1076)
    (h20065 : (¬ p14) ∨ (¬ p106) ∨ (¬ p1038) ∨ (¬ p1077) ∨ (¬ p1141)) : p423 ∨ (¬ p1038) ∨ p1076 ∨ (¬ p14) ∨ (¬ p106) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p1038 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20065 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step32095 (p49 p63 p71 p85 p423 p1140 p1141 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26835 : p85 ∨ p63)
    (h18212 : (¬ p49) ∨ (¬ p71) ∨ (¬ p85) ∨ (¬ p1140) ∨ (¬ p1141)) : p423 ∨ (¬ p1140) ∨ (¬ p49) ∨ (¬ p71) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18212 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)

theorem step32097 (p6 p21 p71 p127 p495 : Prop)
    (h26839 : p127 ∨ p6)
    (h5073 : (¬ p21) ∨ (¬ p71) ∨ (¬ p127) ∨ (¬ p495)) : (¬ p71) ∨ (¬ p21) ∨ (¬ p495) ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p21 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h5073 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)

theorem step32098 (p6 p71 p121 p127 p420 p455 p456 p601 : Prop)
    (h26871 : p456 ∨ p455)
    (h26839 : p127 ∨ p6)
    (h26881 : p601 ∨ p420)
    (h17815 : (¬ p71) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p456) ∨ (¬ p601)) : p455 ∨ (¬ p121) ∨ p6 ∨ p420 ∨ (¬ p71) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17815 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)

theorem step32099 (p6 p10 p71 p127 p323 p420 p633 : Prop)
    (h26861 : p323 ∨ p10)
    (h26839 : p127 ∨ p6)
    (h17862 : (¬ p71) ∨ (¬ p127) ∨ (¬ p323) ∨ (¬ p420) ∨ (¬ p633)) : (¬ p420) ∨ (¬ p71) ∨ p10 ∨ p6 ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
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
  rcases h17862 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)

theorem step32100 (p6 p18 p71 p127 p400 p423 p713 p897 p1000 p1226 p1325 p1333 : Prop)
    (h26839 : p127 ∨ p6)
    (h26931 : p1333 ∨ p1325)
    (h18585 : (¬ p18) ∨ (¬ p71) ∨ (¬ p127) ∨ (¬ p400) ∨ (¬ p423) ∨ (¬ p713) ∨ (¬ p897) ∨ (¬ p1000) ∨ (¬ p1226) ∨ (¬ p1333)) : (¬ p400) ∨ (¬ p71) ∨ p6 ∨ (¬ p423) ∨ (¬ p897) ∨ (¬ p1226) ∨ (¬ p1000) ∨ (¬ p713) ∨ p1325 ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p400 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p713 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h18585 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u11)

theorem step32101 (p6 p16 p71 p127 p134 p189 : Prop)
    (h26839 : p127 ∨ p6)
    (h18655 : (¬ p16) ∨ (¬ p71) ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p189)) : (¬ p71) ∨ p6 ∨ (¬ p189) ∨ (¬ p16) ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18655 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u2)

theorem step32103 (p6 p18 p71 p127 p595 p616 p1190 : Prop)
    (h26883 : p616 ∨ p595)
    (h26839 : p127 ∨ p6)
    (h20589 : (¬ p18) ∨ (¬ p71) ∨ (¬ p127) ∨ (¬ p616) ∨ (¬ p1190)) : (¬ p1190) ∨ p595 ∨ (¬ p18) ∨ p6 ∨ (¬ p71) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p595) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20589 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)

theorem step32104 (p6 p8 p18 p71 p127 p225 p423 p1040 p1055 : Prop)
    (h26839 : p127 ∨ p6)
    (h19362 : (¬ p8) ∨ (¬ p18) ∨ (¬ p71) ∨ (¬ p127) ∨ (¬ p225) ∨ (¬ p423) ∨ (¬ p1040) ∨ (¬ p1055)) : (¬ p18) ∨ (¬ p225) ∨ p6 ∨ (¬ p71) ∨ (¬ p1055) ∨ (¬ p423) ∨ (¬ p8) ∨ (¬ p1040) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1040 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19362 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step32106 (p6 p16 p18 p71 p127 p185 p234 p542 p667 p1115 : Prop)
    (h26839 : p127 ∨ p6)
    (h17725 : (¬ p16) ∨ (¬ p18) ∨ (¬ p71) ∨ (¬ p127) ∨ (¬ p185) ∨ (¬ p234) ∨ (¬ p542) ∨ (¬ p667) ∨ (¬ p1115)) : (¬ p71) ∨ (¬ p1115) ∨ (¬ p234) ∨ (¬ p667) ∨ (¬ p542) ∨ (¬ p18) ∨ (¬ p16) ∨ p6 ∨ (¬ p185) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p667 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h17725 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u3)
  · exact False.elim (q8 u1)

theorem step32108 (p6 p14 p16 p18 p71 p127 p789 p790 p814 p858 p1325 : Prop)
    (h26839 : p127 ∨ p6)
    (h26893 : p814 ∨ p790)
    (h26897 : p858 ∨ p789)
    (h17869 : (¬ p14) ∨ (¬ p16) ∨ (¬ p18) ∨ (¬ p71) ∨ (¬ p127) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1325)) : (¬ p1325) ∨ (¬ p71) ∨ p6 ∨ (¬ p16) ∨ (¬ p18) ∨ (¬ p14) ∨ p790 ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h17869 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u0)

theorem step32109 (p6 p8 p14 p16 p18 p71 p127 p172 p238 p710 p836 p840 : Prop)
    (h26839 : p127 ∨ p6)
    (h26895 : p840 ∨ p836)
    (h26889 : p710 ∨ p8)
    (h17887 : (¬ p14) ∨ (¬ p16) ∨ (¬ p18) ∨ (¬ p71) ∨ (¬ p127) ∨ (¬ p172) ∨ (¬ p238) ∨ (¬ p710) ∨ (¬ p840)) : (¬ p18) ∨ p6 ∨ p836 ∨ (¬ p172) ∨ (¬ p238) ∨ (¬ p16) ∨ (¬ p14) ∨ (¬ p71) ∨ p8 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p172 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h17887 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u11)
  · exact False.elim (q8 u10)

theorem step32110 (p6 p14 p16 p18 p71 p127 p185 p224 p836 : Prop)
    (h26839 : p127 ∨ p6)
    (h19061 : (¬ p14) ∨ (¬ p16) ∨ (¬ p18) ∨ (¬ p71) ∨ (¬ p127) ∨ (¬ p185) ∨ (¬ p224) ∨ (¬ p836)) : (¬ p836) ∨ (¬ p224) ∨ (¬ p185) ∨ (¬ p14) ∨ p6 ∨ (¬ p16) ∨ (¬ p71) ∨ (¬ p18) := by
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
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19061 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u0)

theorem step32111 (p6 p18 p49 p63 p71 p85 p127 : Prop)
    (h26839 : p127 ∨ p6)
    (h26835 : p85 ∨ p63)
    (h16155 : (¬ p18) ∨ (¬ p49) ∨ (¬ p71) ∨ (¬ p85) ∨ (¬ p127)) : (¬ p71) ∨ (¬ p18) ∨ p6 ∨ (¬ p49) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16155 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step32112 (p6 p18 p43 p71 p127 p924 p1096 p1099 : Prop)
    (h26839 : p127 ∨ p6)
    (h26913 : p1099 ∨ p1096)
    (h19597 : (¬ p18) ∨ (¬ p43) ∨ (¬ p71) ∨ (¬ p127) ∨ (¬ p924) ∨ (¬ p1099)) : (¬ p71) ∨ p6 ∨ p1096 ∨ (¬ p18) ∨ (¬ p43) ∨ (¬ p924) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19597 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u7)

theorem step32113 (p6 p18 p43 p71 p127 p1229 p1232 p1270 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h26839 : p127 ∨ p6)
    (h20124 : (¬ p18) ∨ (¬ p43) ∨ (¬ p71) ∨ (¬ p127) ∨ (¬ p1232) ∨ (¬ p1270)) : (¬ p1270) ∨ (¬ p71) ∨ (¬ p43) ∨ p1229 ∨ (¬ p18) ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1270 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20124 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u0)

theorem step32114 (p2 p16 p71 p185 p303 p347 p419 p481 p836 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h26873 : p481 ∨ p2)
    (h17886 : (¬ p16) ∨ (¬ p71) ∨ (¬ p185) ∨ (¬ p303) ∨ (¬ p347) ∨ (¬ p481) ∨ (¬ p836) ∨ (¬ p996)) : p419 ∨ (¬ p71) ∨ (¬ p303) ∨ (¬ p836) ∨ p2 ∨ (¬ p347) ∨ (¬ p185) ∨ (¬ p16) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p16 := by
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
    · exact False.elim (u4 q1)
  rcases h17886 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u8)

theorem step32115 (p2 p16 p71 p185 p303 p348 p481 p836 p1366 : Prop)
    (h26873 : p481 ∨ p2)
    (h26147 : (¬ p1366) ∨ (¬ p303) ∨ (¬ p16) ∨ (¬ p185) ∨ (¬ p481) ∨ (¬ p71) ∨ (¬ p836) ∨ (¬ p348)) : (¬ p1366) ∨ (¬ p836) ∨ (¬ p16) ∨ p2 ∨ (¬ p348) ∨ (¬ p303) ∨ (¬ p185) ∨ (¬ p71) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h26147 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u4)

theorem step32116 (p8 p14 p71 p305 p344 p423 p710 p1076 p1140 p1141 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26889 : p710 ∨ p8)
    (h26148 : (¬ p1076) ∨ (¬ p305) ∨ (¬ p344) ∨ (¬ p14) ∨ (¬ p710) ∨ (¬ p1140) ∨ (¬ p1141) ∨ (¬ p71)) : (¬ p344) ∨ (¬ p1076) ∨ (¬ p1140) ∨ p423 ∨ (¬ p305) ∨ (¬ p14) ∨ p8 ∨ (¬ p71) := by
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
  have u2 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p423) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h26148 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u7)

theorem step32118 (p88 p189 p422 p726 p924 p1044 p1076 p1077 p1562 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h18946 : (¬ p88) ∨ (¬ p189) ∨ (¬ p422) ∨ (¬ p726) ∨ (¬ p924) ∨ (¬ p1044) ∨ (¬ p1077) ∨ (¬ p1562)) : (¬ p1562) ∨ (¬ p1044) ∨ (¬ p924) ∨ (¬ p422) ∨ p1076 ∨ (¬ p88) ∨ (¬ p189) ∨ (¬ p726) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1562 := by
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
  have u3 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18946 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u0)

theorem step32119 (p88 p189 p422 p495 p577 p639 p1044 p1076 p1077 p1096 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h18976 : (¬ p88) ∨ (¬ p189) ∨ (¬ p422) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p639) ∨ (¬ p1044) ∨ (¬ p1077) ∨ (¬ p1096)) : (¬ p422) ∨ p1076 ∨ (¬ p189) ∨ (¬ p1096) ∨ (¬ p1044) ∨ (¬ p88) ∨ (¬ p577) ∨ (¬ p495) ∨ (¬ p639) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1044 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p639 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18976 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u3)

theorem step32120 (p88 p189 p422 p595 p924 p1096 p1099 p1286 p1465 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h19800 : (¬ p88) ∨ (¬ p189) ∨ (¬ p422) ∨ (¬ p595) ∨ (¬ p924) ∨ (¬ p1099) ∨ (¬ p1286) ∨ (¬ p1465)) : (¬ p595) ∨ (¬ p1286) ∨ p1096 ∨ (¬ p189) ∨ (¬ p924) ∨ (¬ p422) ∨ (¬ p1465) ∨ (¬ p88) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19800 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u6)

theorem step32122 (p17 p140 p189 p256 p422 p1209 : Prop)
    (h26853 : p256 ∨ p17)
    (h18381 : (¬ p140) ∨ (¬ p189) ∨ (¬ p256) ∨ (¬ p422) ∨ (¬ p1209)) : p17 ∨ (¬ p422) ∨ (¬ p140) ∨ (¬ p1209) ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p17) := fun hu => hn (Or.inl hu)
  have u1 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h18381 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)

theorem step32123 (p48 p68 p124 p224 p304 p344 p346 p422 p425 p582 p1140 p1713 : Prop)
    (h26863 : p346 ∨ p344)
    (h26859 : p304 ∨ p124)
    (h18844 : (¬ p48) ∨ (¬ p68) ∨ (¬ p224) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p422) ∨ (¬ p425) ∨ (¬ p582) ∨ (¬ p1140) ∨ (¬ p1713)) : (¬ p1713) ∨ (¬ p422) ∨ (¬ p1140) ∨ p344 ∨ (¬ p425) ∨ (¬ p582) ∨ (¬ p48) ∨ p124 ∨ (¬ p224) ∨ (¬ p68) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1713 := by
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
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h18844 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u2)
  · exact False.elim (q9 u0)

theorem step32124 (p47 p422 p423 p1256 : Prop)
    (h26929 : p1256 ∨ p422)
    (h11274 : (¬ p47) ∨ p423 ∨ (¬ p1256)) : p423 ∨ (¬ p47) ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p422) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h11274 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)

theorem step32127 (p6 p18 p19 p234 p419 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26829 : p19 ∨ p18)
    (h17113 : (¬ p6) ∨ (¬ p19) ∨ (¬ p419) ∨ (¬ p1187)) : p234 ∨ p18 ∨ (¬ p419) ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p18) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17113 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step32129 (p234 p303 p434 p435 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h20356 : (¬ p303) ∨ (¬ p434) ∨ (¬ p435) ∨ (¬ p1187)) : (¬ p434) ∨ (¬ p435) ∨ (¬ p303) ∨ p234 := by
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
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p234) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20356 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)

theorem step32131 (p15 p69 p86 p224 p234 p545 p789 p790 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26833 : p69 ∨ p15)
    (h19721 : (¬ p69) ∨ (¬ p86) ∨ (¬ p224) ∨ (¬ p545) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1187)) : (¬ p789) ∨ p234 ∨ (¬ p224) ∨ (¬ p790) ∨ (¬ p86) ∨ p15 ∨ (¬ p545) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p234) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19721 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step32132 (p72 p211 p234 p368 p382 p406 p419 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26869 : p406 ∨ p382)
    (h17782 : (¬ p72) ∨ (¬ p211) ∨ (¬ p368) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p1187)) : p234 ∨ p382 ∨ (¬ p72) ∨ (¬ p211) ∨ (¬ p368) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17782 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)

theorem step32133 (p234 p423 p997 p1141 p1187 : Prop)
    (h26916 : (¬ p423) ∨ (¬ p1141))
    (h26921 : p1187 ∨ p234)
    (h14016 : (¬ p997) ∨ p1141 ∨ (¬ p1187)) : (¬ p423) ∨ p234 ∨ (¬ p997) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p234) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p997 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1141) := by
    rcases h26916 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u4 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h14016 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)

theorem step32134 (p1 p14 p234 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h10566 : (¬ p1) ∨ (¬ p14) ∨ (¬ p1187)) : (¬ p1) ∨ p234 ∨ (¬ p14) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p234) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h10566 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)

theorem step32135 (p163 p167 p234 p884 p940 p1187 p1562 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26843 : p167 ∨ p163)
    (h18852 : (¬ p167) ∨ (¬ p884) ∨ (¬ p940) ∨ (¬ p1187) ∨ (¬ p1562)) : (¬ p1562) ∨ p234 ∨ (¬ p884) ∨ p163 ∨ (¬ p940) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1562 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p234) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p884 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18852 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)

theorem step32138 (p2 p41 p45 p192 p303 p387 p419 : Prop)
    (h26831 : p45 ∨ p41)
    (h26867 : p387 ∨ p303)
    (h20371 : (¬ p2) ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p387) ∨ (¬ p419)) : (¬ p2) ∨ (¬ p192) ∨ p41 ∨ (¬ p419) ∨ p303 := by
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
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20371 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)

theorem step32140 (p6 p41 p45 p90 p101 p185 p192 p224 p237 p657 p836 p840 : Prop)
    (h26887 : p657 ∨ p224)
    (h26895 : p840 ∨ p836)
    (h26851 : p237 ∨ p185)
    (h26586 : p90)
    (h26831 : p45 ∨ p41)
    (h19694 : (¬ p6) ∨ (¬ p45) ∨ (¬ p90) ∨ (¬ p101) ∨ (¬ p192) ∨ (¬ p237) ∨ (¬ p657) ∨ (¬ p840)) : (¬ p101) ∨ p224 ∨ p836 ∨ p185 ∨ (¬ p192) ∨ (¬ p6) ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p90 := by
    exact h26586
  have u11 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19694 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u11)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u8)

theorem step32141 (p6 p17 p41 p45 p90 p101 p126 p192 p256 p350 : Prop)
    (h26853 : p256 ∨ p17)
    (h26831 : p45 ∨ p41)
    (h26586 : p90)
    (h20373 : (¬ p6) ∨ (¬ p45) ∨ (¬ p90) ∨ (¬ p101) ∨ (¬ p126) ∨ (¬ p192) ∨ (¬ p256) ∨ (¬ p350)) : p17 ∨ p41 ∨ (¬ p350) ∨ (¬ p101) ∨ (¬ p126) ∨ (¬ p192) ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p17) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p41) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p350 := by
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
  have u6 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p90 := by
    exact h26586
  rcases h20373 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u2)

theorem step32144 (p2 p41 p45 p140 p192 p326 p576 p581 : Prop)
    (h26879 : p581 ∨ p576)
    (h26831 : p45 ∨ p41)
    (h20426 : (¬ p2) ∨ (¬ p45) ∨ (¬ p140) ∨ (¬ p192) ∨ (¬ p326) ∨ (¬ p581)) : (¬ p2) ∨ p576 ∨ (¬ p140) ∨ p41 ∨ (¬ p326) ∨ (¬ p192) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p326 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20426 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)

theorem step32145 (p41 p45 p140 p192 p576 p581 p1140 p1159 p1209 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26879 : p581 ∨ p576)
    (h26831 : p45 ∨ p41)
    (h18558 : (¬ p45) ∨ (¬ p140) ∨ (¬ p192) ∨ (¬ p581) ∨ (¬ p1159) ∨ (¬ p1209)) : p1140 ∨ p576 ∨ (¬ p192) ∨ (¬ p1209) ∨ p41 ∨ (¬ p140) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18558 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)

theorem step32146 (p17 p41 p45 p90 p126 p192 p256 p331 p382 p419 p477 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h26853 : p256 ∨ p17)
    (h26586 : p90)
    (h26831 : p45 ∨ p41)
    (h18275 : (¬ p45) ∨ (¬ p90) ∨ (¬ p126) ∨ (¬ p192) ∨ (¬ p256) ∨ (¬ p331) ∨ (¬ p382) ∨ (¬ p477) ∨ (¬ p996)) : (¬ p477) ∨ p419 ∨ p17 ∨ (¬ p331) ∨ (¬ p192) ∨ p41 ∨ (¬ p382) ∨ (¬ p126) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p477 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p419) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p331 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p90 := by
    exact h26586
  have u11 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18275 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u11)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u0)
  · exact False.elim (q8 u8)

theorem step32147 (p3 p17 p41 p45 p90 p126 p192 p225 p226 p256 p347 : Prop)
    (h26847 : p226 ∨ p3)
    (h26831 : p45 ∨ p41)
    (h26586 : p90)
    (h26853 : p256 ∨ p17)
    (h18528 : (¬ p45) ∨ (¬ p90) ∨ (¬ p126) ∨ (¬ p192) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p256) ∨ (¬ p347)) : p3 ∨ p41 ∨ p17 ∨ (¬ p192) ∨ (¬ p225) ∨ (¬ p347) ∨ (¬ p126) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p41) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p90 := by
    exact h26586
  have u10 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18528 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u5)

theorem step32148 (p6 p41 p45 p192 p330 p801 p1385 p1393 : Prop)
    (h26831 : p45 ∨ p41)
    (h26933 : p1393 ∨ p1385)
    (h18042 : (¬ p6) ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p330) ∨ (¬ p801) ∨ (¬ p1393)) : (¬ p192) ∨ p41 ∨ (¬ p6) ∨ (¬ p330) ∨ (¬ p801) ∨ p1385 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p41) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
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
  have u5 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18042 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u7)

theorem step32149 (p2 p192 p422 p997 p1256 : Prop)
    (h26929 : p1256 ∨ p422)
    (h11958 : (¬ p2) ∨ (¬ p192) ∨ (¬ p997) ∨ (¬ p1256)) : (¬ p2) ∨ p422 ∨ (¬ p192) ∨ (¬ p997) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p422) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p997 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h11958 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step32178 (p161 p642 p980 p1076 p1225 p1311 : Prop)
    (h26925 : p1225 ∨ p161)
    (h16991 : (¬ p642) ∨ (¬ p980) ∨ (¬ p1076) ∨ (¬ p1225) ∨ (¬ p1311)) : (¬ p980) ∨ p161 ∨ (¬ p1311) ∨ (¬ p1076) ∨ (¬ p642) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p161) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1311 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p642 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16991 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)

theorem step32179 (p63 p918 p928 p1076 p1115 p1116 : Prop)
    (h26901 : p928 ∨ p918)
    (h26915 : p1116 ∨ p1115)
    (h17450 : (¬ p63) ∨ (¬ p928) ∨ (¬ p1076) ∨ (¬ p1116)) : p918 ∨ (¬ p1076) ∨ (¬ p63) ∨ p1115 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p918) := fun hu => hn (Or.inl hu)
  have u1 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17450 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)

theorem step32182 (p124 p189 p193 p267 p304 p980 p1076 p1469 p1713 : Prop)
    (h26859 : p304 ∨ p124)
    (h26845 : p193 ∨ p189)
    (h18706 : (¬ p193) ∨ (¬ p267) ∨ (¬ p304) ∨ (¬ p980) ∨ (¬ p1076) ∨ (¬ p1469) ∨ (¬ p1713)) : (¬ p1713) ∨ p124 ∨ p189 ∨ (¬ p1469) ∨ (¬ p1076) ∨ (¬ p980) ∨ (¬ p267) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1713 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1469 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p267 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18706 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u0)

theorem step32183 (p10 p101 p126 p301 p323 p663 p1076 : Prop)
    (h26857 : p301 ∨ p126)
    (h26861 : p323 ∨ p10)
    (h18336 : (¬ p101) ∨ (¬ p301) ∨ (¬ p323) ∨ (¬ p663) ∨ (¬ p1076)) : p126 ∨ (¬ p101) ∨ p10 ∨ (¬ p1076) ∨ (¬ p663) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p663 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18336 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)

theorem step32184 (p124 p134 p210 p304 p980 p1076 : Prop)
    (h26859 : p304 ∨ p124)
    (h20357 : (¬ p134) ∨ (¬ p210) ∨ (¬ p304) ∨ (¬ p980) ∨ (¬ p1076)) : (¬ p210) ∨ p124 ∨ (¬ p1076) ∨ (¬ p980) ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20357 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)

theorem step32185 (p124 p304 p595 p980 p1076 p1330 p1542 : Prop)
    (h26859 : p304 ∨ p124)
    (h26150 : (¬ p1542) ∨ (¬ p980) ∨ (¬ p1330) ∨ (¬ p304) ∨ (¬ p595) ∨ (¬ p1076)) : (¬ p1542) ∨ p124 ∨ (¬ p595) ∨ (¬ p1330) ∨ (¬ p1076) ∨ (¬ p980) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h26150 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u4)

theorem step32207 (p101 p102 p106 p111 p112 p113 p114 p115 : Prop)
    (h26836 : (¬ p101) ∨ (¬ p102))
    (h542 : p102 ∨ p106 ∨ (¬ p111) ∨ (¬ p112) ∨ (¬ p113) ∨ (¬ p114) ∨ (¬ p115)) : (¬ p113) ∨ (¬ p114) ∨ (¬ p101) ∨ (¬ p115) ∨ p106 ∨ (¬ p112) ∨ (¬ p111) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p113 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p114 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p106) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p112 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p111 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p102) := by
    rcases h26836 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h542 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u7 q0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u3)

theorem step32211 (p63 p225 p836 p840 p918 p928 : Prop)
    (h26901 : p928 ∨ p918)
    (h26895 : p840 ∨ p836)
    (h18635 : (¬ p63) ∨ (¬ p225) ∨ (¬ p840) ∨ (¬ p928)) : p918 ∨ (¬ p225) ∨ (¬ p63) ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p918) := fun hu => hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18635 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step32212 (p3 p5 p63 p126 p225 p226 p347 p576 p581 : Prop)
    (h26847 : p226 ∨ p3)
    (h26879 : p581 ∨ p576)
    (h17973 : (¬ p5) ∨ (¬ p63) ∨ (¬ p126) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p347) ∨ (¬ p581)) : p3 ∨ (¬ p347) ∨ (¬ p63) ∨ (¬ p225) ∨ (¬ p5) ∨ p576 ∨ (¬ p126) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p126 := by
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
    · exact False.elim (u5 q1)
  rcases h17973 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u8)

theorem step32213 (p3 p5 p63 p224 p225 p226 p860 p1273 : Prop)
    (h26847 : p226 ∨ p3)
    (h18072 : (¬ p5) ∨ (¬ p63) ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p860) ∨ (¬ p1273)) : p3 ∨ (¬ p1273) ∨ (¬ p224) ∨ (¬ p63) ∨ (¬ p5) ∨ (¬ p860) ∨ (¬ p225) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p860 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h18072 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u1)

theorem step32214 (p14 p47 p87 p125 p189 p225 p229 p262 p347 p362 p576 p581 : Prop)
    (h26849 : p229 ∨ p14)
    (h26879 : p581 ∨ p576)
    (h26865 : p362 ∨ p125)
    (h18984 : (¬ p47) ∨ (¬ p87) ∨ (¬ p189) ∨ (¬ p225) ∨ (¬ p229) ∨ (¬ p262) ∨ (¬ p347) ∨ (¬ p362) ∨ (¬ p581)) : p14 ∨ p576 ∨ (¬ p87) ∨ p125 ∨ (¬ p225) ∨ (¬ p189) ∨ (¬ p262) ∨ (¬ p347) ∨ (¬ p47) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u11 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18984 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u11)
  · exact False.elim (q8 u10)

theorem step32215 (p3 p5 p225 p226 p495 p499 p633 p668 p1076 p1077 : Prop)
    (h26847 : p226 ∨ p3)
    (h26911 : p1077 ∨ p1076)
    (h26875 : p499 ∨ p495)
    (h19448 : (¬ p5) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p668) ∨ (¬ p1077)) : p3 ∨ (¬ p225) ∨ p1076 ∨ (¬ p633) ∨ p495 ∨ (¬ p5) ∨ (¬ p668) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p668 := by
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
    · exact False.elim (u2 q1)
  have u9 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19448 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u8)

theorem step32217 (p163 p167 p189 p225 p734 : Prop)
    (h26843 : p167 ∨ p163)
    (h17941 : (¬ p167) ∨ (¬ p189) ∨ (¬ p225) ∨ (¬ p734)) : p163 ∨ (¬ p225) ∨ (¬ p734) ∨ (¬ p189) := by
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
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17941 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)

theorem step32218 (p163 p167 p189 p225 p263 p303 p347 p368 p382 p406 : Prop)
    (h26843 : p167 ∨ p163)
    (h26869 : p406 ∨ p382)
    (h19932 : (¬ p167) ∨ (¬ p189) ∨ (¬ p225) ∨ (¬ p263) ∨ (¬ p303) ∨ (¬ p347) ∨ (¬ p368) ∨ (¬ p406)) : p163 ∨ (¬ p225) ∨ (¬ p368) ∨ (¬ p189) ∨ (¬ p303) ∨ (¬ p263) ∨ p382 ∨ (¬ p347) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p163) := fun hu => hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p263 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19932 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u9)

theorem step32219 (p3 p6 p127 p224 p225 p226 : Prop)
    (h26847 : p226 ∨ p3)
    (h26839 : p127 ∨ p6)
    (h16364 : (¬ p127) ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p226)) : p3 ∨ p6 ∨ (¬ p225) ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
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
  rcases h16364 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step32221 (p3 p38 p49 p63 p85 p225 p226 p668 p926 p1096 p1115 p1116 : Prop)
    (h26847 : p226 ∨ p3)
    (h26835 : p85 ∨ p63)
    (h26915 : p1116 ∨ p1115)
    (h16696 : (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p668) ∨ (¬ p926) ∨ (¬ p1096) ∨ (¬ p1116)) : p3 ∨ (¬ p225) ∨ p63 ∨ p1115 ∨ (¬ p38) ∨ (¬ p1096) ∨ (¬ p926) ∨ (¬ p49) ∨ (¬ p668) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p926 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16696 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u11)

theorem step32222 (p3 p41 p45 p90 p185 p192 p225 p226 p237 p668 p923 p1095 : Prop)
    (h26847 : p226 ∨ p3)
    (h26586 : p90)
    (h26831 : p45 ∨ p41)
    (h26851 : p237 ∨ p185)
    (h20380 : (¬ p45) ∨ (¬ p90) ∨ (¬ p192) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p237) ∨ (¬ p668) ∨ (¬ p923) ∨ (¬ p1095)) : p3 ∨ (¬ p923) ∨ (¬ p1095) ∨ (¬ p225) ∨ (¬ p668) ∨ p41 ∨ p185 ∨ (¬ p192) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p923 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p192 := by
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
    · exact False.elim (u5 q1)
  have u11 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20380 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u2)

theorem step32223 (p8 p12 p39 p63 p68 p225 p561 p1229 p1232 p1313 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h20472 : (¬ p8) ∨ (¬ p12) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p225) ∨ (¬ p561) ∨ (¬ p1232) ∨ (¬ p1313)) : (¬ p12) ∨ (¬ p68) ∨ (¬ p225) ∨ (¬ p39) ∨ (¬ p561) ∨ p1229 ∨ (¬ p1313) ∨ (¬ p8) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1313 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20472 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u6)

theorem step32224 (p3 p6 p127 p225 p226 p344 : Prop)
    (h26847 : p226 ∨ p3)
    (h26839 : p127 ∨ p6)
    (h17045 : (¬ p127) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p344)) : p3 ∨ p6 ∨ (¬ p344) ∨ (¬ p225) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p225 := by
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
  rcases h17045 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)

theorem step32225 (p12 p225 p662 p1036 : Prop)
    (h26906 : (¬ p12) ∨ (¬ p1036))
    (h14227 : (¬ p225) ∨ (¬ p662) ∨ p1036) : (¬ p12) ∨ (¬ p225) ∨ (¬ p662) := by
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
  have u2 : p662 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1036) := by
    rcases h26906 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h14227 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (u3 q2)

theorem step32226 (p12 p225 p1074 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h19474 : (¬ p12) ∨ (¬ p225) ∨ (¬ p1074) ∨ (¬ p1099)) : (¬ p12) ∨ (¬ p225) ∨ (¬ p1074) ∨ p1096 := by
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
  have u3 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19474 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step32232 (p63 p85 p734 p836 p918 : Prop)
    (h26835 : p85 ∨ p63)
    (h17099 : (¬ p85) ∨ (¬ p734) ∨ (¬ p836) ∨ (¬ p918)) : (¬ p734) ∨ (¬ p836) ∨ (¬ p918) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17099 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)

theorem step32233 (p17 p185 p256 p303 p348 p836 : Prop)
    (h26853 : p256 ∨ p17)
    (h20039 : (¬ p185) ∨ (¬ p256) ∨ (¬ p303) ∨ (¬ p348) ∨ (¬ p836)) : (¬ p185) ∨ (¬ p836) ∨ (¬ p348) ∨ (¬ p303) ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20039 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u1)

theorem step32234 (p344 p638 p836 p1074 p1115 p1116 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h19577 : (¬ p344) ∨ (¬ p638) ∨ (¬ p836) ∨ (¬ p1074) ∨ (¬ p1116)) : (¬ p836) ∨ (¬ p344) ∨ p1115 ∨ (¬ p638) ∨ (¬ p1074) := by
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
  have u2 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p638 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19577 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)

theorem step32235 (p836 p1074 p1096 p1099 p1115 p1116 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h26913 : p1099 ∨ p1096)
    (h20165 : (¬ p836) ∨ (¬ p1074) ∨ (¬ p1099) ∨ (¬ p1116)) : p1115 ∨ (¬ p836) ∨ p1096 ∨ (¬ p1074) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1115) := fun hu => hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20165 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step32238 (p364 p382 p406 p594 p633 p1287 : Prop)
    (h26869 : p406 ∨ p382)
    (h24218 : (¬ p364) ∨ (¬ p594) ∨ (¬ p406) ∨ (¬ p1287) ∨ (¬ p633)) : (¬ p594) ∨ (¬ p364) ∨ p382 ∨ (¬ p633) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p594 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p364 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h24218 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)

theorem step32241 (p25 p44 p124 p261 p304 p633 p790 : Prop)
    (h26859 : p304 ∨ p124)
    (h26153 : (¬ p790) ∨ (¬ p304) ∨ (¬ p44) ∨ (¬ p633) ∨ (¬ p25) ∨ (¬ p261)) : (¬ p44) ∨ p124 ∨ (¬ p633) ∨ (¬ p25) ∨ (¬ p261) ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p25 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h26153 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step32242 (p25 p50 p124 p134 p210 p304 p633 : Prop)
    (h26859 : p304 ∨ p124)
    (h16907 : (¬ p25) ∨ (¬ p50) ∨ (¬ p134) ∨ (¬ p210) ∨ (¬ p304) ∨ (¬ p633)) : (¬ p50) ∨ (¬ p210) ∨ (¬ p25) ∨ (¬ p633) ∨ p124 ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p50 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p25 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16907 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)

theorem step32243 (p283 p583 p633 p1076 p1077 p1115 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h18767 : (¬ p283) ∨ (¬ p583) ∨ (¬ p633) ∨ (¬ p1077) ∨ (¬ p1115)) : (¬ p1115) ∨ p1076 ∨ (¬ p633) ∨ (¬ p283) ∨ (¬ p583) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p283 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p583 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18767 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)

theorem step32244 (p25 p124 p210 p234 p304 p326 p633 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26859 : p304 ∨ p124)
    (h20196 : (¬ p25) ∨ (¬ p210) ∨ (¬ p304) ∨ (¬ p326) ∨ (¬ p633) ∨ (¬ p1187)) : p234 ∨ (¬ p210) ∨ (¬ p633) ∨ p124 ∨ (¬ p25) ∨ (¬ p326) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p25 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p326 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20196 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)

theorem step32245 (p124 p160 p304 p532 p633 p961 : Prop)
    (h26859 : p304 ∨ p124)
    (h21512 : (¬ p160) ∨ (¬ p633) ∨ (¬ p532) ∨ p961 ∨ (¬ p304)) : (¬ p160) ∨ p124 ∨ p961 ∨ (¬ p532) ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p961) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h21512 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (u2 q3)
  · exact False.elim (q4 u5)

theorem step32247 (p41 p45 p89 p189 p193 p258 p580 p633 : Prop)
    (h26845 : p193 ∨ p189)
    (h26831 : p45 ∨ p41)
    (h17387 : (¬ p45) ∨ (¬ p89) ∨ (¬ p193) ∨ (¬ p258) ∨ (¬ p580) ∨ (¬ p633)) : p189 ∨ (¬ p258) ∨ (¬ p89) ∨ (¬ p633) ∨ p41 ∨ (¬ p580) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p189) := fun hu => hn (Or.inl hu)
  have u1 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p580 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17387 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u3)

theorem step32248 (p124 p265 p304 p516 p580 p633 p1385 : Prop)
    (h26859 : p304 ∨ p124)
    (h17371 : (¬ p265) ∨ (¬ p304) ∨ (¬ p516) ∨ (¬ p580) ∨ (¬ p633) ∨ (¬ p1385)) : (¬ p516) ∨ p124 ∨ (¬ p580) ∨ (¬ p633) ∨ (¬ p1385) ∨ (¬ p265) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p516 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p580 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17371 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step32249 (p5 p17 p89 p256 p533 p574 p633 p756 p1140 p1159 p1465 : Prop)
    (h26853 : p256 ∨ p17)
    (h26919 : p1159 ∨ p1140)
    (h18217 : (¬ p5) ∨ (¬ p89) ∨ (¬ p256) ∨ (¬ p533) ∨ (¬ p574) ∨ (¬ p633) ∨ (¬ p756) ∨ (¬ p1159) ∨ (¬ p1465)) : (¬ p756) ∨ (¬ p633) ∨ (¬ p574) ∨ (¬ p1465) ∨ (¬ p89) ∨ (¬ p533) ∨ p17 ∨ (¬ p5) ∨ p1140 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p574 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h18217 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u3)

theorem step32250 (p8 p15 p423 p710 p734 p1035 p1103 p1335 : Prop)
    (h26889 : p710 ∨ p8)
    (h18650 : (¬ p15) ∨ (¬ p423) ∨ (¬ p710) ∨ (¬ p734) ∨ (¬ p1035) ∨ (¬ p1103) ∨ (¬ p1335)) : (¬ p1035) ∨ (¬ p423) ∨ (¬ p1335) ∨ (¬ p1103) ∨ (¬ p15) ∨ p8 ∨ (¬ p734) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18650 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u2)

theorem step32251 (p15 p18 p19 p108 p225 p344 p346 p544 : Prop)
    (h26877 : p544 ∨ p225)
    (h26863 : p346 ∨ p344)
    (h26829 : p19 ∨ p18)
    (h19320 : (¬ p15) ∨ (¬ p19) ∨ (¬ p108) ∨ (¬ p346) ∨ (¬ p544)) : p225 ∨ (¬ p15) ∨ p344 ∨ (¬ p108) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p225) := fun hu => hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19320 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step32252 (p15 p124 p304 p344 p346 p419 p542 p1193 p1286 : Prop)
    (h26859 : p304 ∨ p124)
    (h26863 : p346 ∨ p344)
    (h26155 : (¬ p1286) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p419) ∨ (¬ p1193) ∨ (¬ p542) ∨ (¬ p15)) : p124 ∨ (¬ p1286) ∨ p344 ∨ (¬ p542) ∨ (¬ p1193) ∨ (¬ p15) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h26155 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u5)

theorem step32253 (p14 p15 p225 p303 p351 p382 p387 p544 p621 : Prop)
    (h26867 : p387 ∨ p303)
    (h26877 : p544 ∨ p225)
    (h19141 : (¬ p14) ∨ (¬ p15) ∨ (¬ p351) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p544) ∨ (¬ p621)) : (¬ p621) ∨ p303 ∨ (¬ p15) ∨ p225 ∨ (¬ p382) ∨ (¬ p351) ∨ (¬ p14) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p621 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19141 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u0)

theorem step32255 (p10 p15 p126 p301 p323 p495 p574 : Prop)
    (h26857 : p301 ∨ p126)
    (h26861 : p323 ∨ p10)
    (h18187 : (¬ p15) ∨ (¬ p301) ∨ (¬ p323) ∨ (¬ p495) ∨ (¬ p574)) : (¬ p15) ∨ p126 ∨ (¬ p574) ∨ (¬ p495) ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p574 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18187 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)

theorem step32257 (p8 p15 p303 p305 p348 p710 p1325 p1469 p1712 : Prop)
    (h26889 : p710 ∨ p8)
    (h26156 : (¬ p1712) ∨ (¬ p305) ∨ (¬ p1469) ∨ (¬ p303) ∨ (¬ p1325) ∨ (¬ p348) ∨ (¬ p15) ∨ (¬ p710)) : (¬ p1712) ∨ (¬ p305) ∨ p8 ∨ (¬ p1469) ∨ (¬ p303) ∨ (¬ p1325) ∨ (¬ p348) ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1712 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1469 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h26156 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u8)

theorem step32260 (p14 p15 p382 p406 p534 p690 p735 p1287 : Prop)
    (h26869 : p406 ∨ p382)
    (h17829 : (¬ p14) ∨ (¬ p15) ∨ (¬ p406) ∨ (¬ p534) ∨ (¬ p690) ∨ (¬ p735) ∨ (¬ p1287)) : (¬ p534) ∨ (¬ p690) ∨ (¬ p1287) ∨ (¬ p14) ∨ (¬ p735) ∨ p382 ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p735 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17829 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u2)

theorem step32263 (p8 p15 p18 p19 p63 p85 p344 p582 p634 p710 p1076 p1102 : Prop)
    (h26835 : p85 ∨ p63)
    (h26889 : p710 ∨ p8)
    (h26829 : p19 ∨ p18)
    (h16377 : (¬ p15) ∨ (¬ p19) ∨ (¬ p85) ∨ (¬ p344) ∨ (¬ p582) ∨ (¬ p634) ∨ (¬ p710) ∨ (¬ p1076) ∨ (¬ p1102)) : (¬ p1102) ∨ (¬ p344) ∨ (¬ p15) ∨ p63 ∨ p8 ∨ p18 ∨ (¬ p634) ∨ (¬ p582) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p634 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h16377 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u11)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u0)

theorem step32265 (p15 p25 p495 p499 : Prop)
    (h26874 : (¬ p495) ∨ (¬ p499))
    (h10583 : (¬ p15) ∨ (¬ p25) ∨ p499) : (¬ p495) ∨ (¬ p25) ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p25 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p499) := by
    rcases h26874 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h10583 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (u3 q2)

theorem step32266 (p14 p15 p163 p167 p422 p1256 : Prop)
    (h26843 : p167 ∨ p163)
    (h26929 : p1256 ∨ p422)
    (h17420 : (¬ p14) ∨ (¬ p15) ∨ (¬ p167) ∨ (¬ p1256)) : (¬ p15) ∨ p163 ∨ p422 ∨ (¬ p14) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17420 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step32267 (p14 p15 p63 p85 p163 p167 : Prop)
    (h26835 : p85 ∨ p63)
    (h26843 : p167 ∨ p163)
    (h16409 : (¬ p14) ∨ (¬ p15) ∨ (¬ p85) ∨ (¬ p167)) : (¬ p15) ∨ (¬ p14) ∨ p63 ∨ p163 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16409 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step32269 (p12 p14 p15 p980 p983 : Prop)
    (h26903 : p983 ∨ p980)
    (h17699 : (¬ p12) ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p983)) : (¬ p12) ∨ p980 ∨ (¬ p15) ∨ (¬ p14) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17699 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step32270 (p15 p49 p84 p242 p285 p495 p633 p636 p1055 p1061 p1115 : Prop)
    (h26885 : p636 ∨ p633)
    (h26909 : p1061 ∨ p1055)
    (h20144 : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p242) ∨ (¬ p285) ∨ (¬ p495) ∨ (¬ p636) ∨ (¬ p1061) ∨ (¬ p1115)) : (¬ p1115) ∨ (¬ p84) ∨ (¬ p49) ∨ (¬ p15) ∨ p633 ∨ (¬ p242) ∨ (¬ p285) ∨ p1055 ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
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
  have u4 : (¬ p633) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p285 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h20144 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u0)

theorem step32271 (p14 p15 p224 p225 p544 p657 : Prop)
    (h26887 : p657 ∨ p224)
    (h26877 : p544 ∨ p225)
    (h17355 : (¬ p14) ∨ (¬ p15) ∨ (¬ p544) ∨ (¬ p657)) : (¬ p15) ∨ p224 ∨ (¬ p14) ∨ p225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17355 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step32272 (p14 p15 p63 p85 p225 p544 : Prop)
    (h26877 : p544 ∨ p225)
    (h26835 : p85 ∨ p63)
    (h16534 : (¬ p14) ∨ (¬ p15) ∨ (¬ p85) ∨ (¬ p544)) : p225 ∨ (¬ p14) ∨ p63 ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p225) := fun hu => hn (Or.inl hu)
  have u1 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16534 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step32294 (p41 p45 p48 : Prop)
    (h26830 : (¬ p41) ∨ (¬ p45))
    (h25104 : p48 ∨ p45) : p48 ∨ (¬ p41) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p48) := fun hu => hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p45) := by
    rcases h26830 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h25104 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step32300 (p422 p424 p431 p435 p796 p1001 p1256 : Prop)
    (h26891 : p796 ∨ p424)
    (h26929 : p1256 ∨ p422)
    (h17194 : (¬ p431) ∨ (¬ p435) ∨ (¬ p796) ∨ (¬ p1001) ∨ (¬ p1256)) : p424 ∨ (¬ p431) ∨ (¬ p435) ∨ (¬ p1001) ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1001 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17194 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)

theorem step32301 (p422 p424 p435 p728 p796 p1256 : Prop)
    (h26891 : p796 ∨ p424)
    (h26929 : p1256 ∨ p422)
    (h16753 : (¬ p435) ∨ (¬ p728) ∨ (¬ p796) ∨ (¬ p1256)) : p424 ∨ p422 ∨ (¬ p435) ∨ (¬ p728) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p422) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16753 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step32302 (p189 p419 p424 p796 p1325 : Prop)
    (h26891 : p796 ∨ p424)
    (h19787 : (¬ p189) ∨ (¬ p419) ∨ (¬ p796) ∨ (¬ p1325)) : p424 ∨ (¬ p189) ∨ (¬ p1325) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p189 := by
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
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19787 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)

theorem step32303 (p189 p224 p419 p424 p657 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h26887 : p657 ∨ p224)
    (h18535 : (¬ p189) ∨ (¬ p419) ∨ (¬ p657) ∨ (¬ p796)) : p424 ∨ p224 ∨ (¬ p419) ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18535 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step32304 (p6 p11 p121 p141 p188 p424 p796 p1206 p1443 : Prop)
    (h26891 : p796 ∨ p424)
    (h26923 : p1206 ∨ p121)
    (h26935 : p1443 ∨ p11)
    (h16864 : (¬ p6) ∨ (¬ p141) ∨ (¬ p188) ∨ (¬ p796) ∨ (¬ p1206) ∨ (¬ p1443)) : p424 ∨ p121 ∨ (¬ p188) ∨ p11 ∨ (¬ p141) ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p121) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16864 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u8)

theorem step32305 (p6 p127 p187 p329 p424 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h26839 : p127 ∨ p6)
    (h5965 : (¬ p127) ∨ (¬ p187) ∨ (¬ p329) ∨ (¬ p796)) : (¬ p187) ∨ p424 ∨ p6 ∨ (¬ p329) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p424) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p329 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h5965 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step32306 (p50 p382 p424 p480 p796 p1193 p1286 : Prop)
    (h26891 : p796 ∨ p424)
    (h18687 : (¬ p50) ∨ (¬ p382) ∨ (¬ p480) ∨ (¬ p796) ∨ (¬ p1193) ∨ (¬ p1286)) : p424 ∨ (¬ p1286) ∨ (¬ p50) ∨ (¬ p480) ∨ (¬ p1193) ∨ (¬ p382) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p50 := by
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
  have u5 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h18687 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u1)

theorem step32307 (p422 p424 p796 p997 p1256 : Prop)
    (h26891 : p796 ∨ p424)
    (h26929 : p1256 ∨ p422)
    (h11994 : (¬ p796) ∨ (¬ p997) ∨ (¬ p1256)) : p424 ∨ p422 ∨ (¬ p997) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p422) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p997 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h11994 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)

theorem step32308 (p189 p303 p349 p387 p419 p424 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h26867 : p387 ∨ p303)
    (h19784 : (¬ p189) ∨ (¬ p349) ∨ (¬ p387) ∨ (¬ p419) ∨ (¬ p796)) : p424 ∨ (¬ p349) ∨ p303 ∨ (¬ p419) ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
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
  have u6 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19784 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)

theorem step32310 (p88 p189 p424 p435 p796 p924 p1229 p1232 p1311 p1547 p1674 : Prop)
    (h26891 : p796 ∨ p424)
    (h26927 : p1232 ∨ p1229)
    (h20018 : (¬ p88) ∨ (¬ p189) ∨ (¬ p435) ∨ (¬ p796) ∨ (¬ p924) ∨ (¬ p1232) ∨ (¬ p1311) ∨ (¬ p1547) ∨ (¬ p1674)) : (¬ p1547) ∨ (¬ p1674) ∨ (¬ p189) ∨ (¬ p88) ∨ (¬ p924) ∨ p424 ∨ p1229 ∨ (¬ p435) ∨ (¬ p1311) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1547 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1674 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p424) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1311 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20018 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u0)
  · exact False.elim (q8 u1)

theorem step32312 (p6 p127 p134 p156 p185 p186 : Prop)
    (h26839 : p127 ∨ p6)
    (h16161 : (¬ p127) ∨ (¬ p134) ∨ (¬ p156) ∨ (¬ p185) ∨ (¬ p186)) : (¬ p185) ∨ p6 ∨ (¬ p134) ∨ (¬ p156) ∨ (¬ p186) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16161 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)

theorem step32313 (p6 p127 p134 p187 : Prop)
    (h26839 : p127 ∨ p6)
    (h921 : (¬ p127) ∨ (¬ p134) ∨ (¬ p187)) : (¬ p187) ∨ (¬ p134) ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h921 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)

theorem step32314 (p6 p127 p134 p186 p422 p1035 p1256 : Prop)
    (h26929 : p1256 ∨ p422)
    (h26839 : p127 ∨ p6)
    (h16751 : (¬ p127) ∨ (¬ p134) ∨ (¬ p186) ∨ (¬ p1035) ∨ (¬ p1256)) : (¬ p1035) ∨ (¬ p134) ∨ p422 ∨ p6 ∨ (¬ p186) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16751 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)

theorem step32316 (p6 p127 p134 p186 p419 p424 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h26839 : p127 ∨ p6)
    (h16919 : (¬ p127) ∨ (¬ p134) ∨ (¬ p186) ∨ (¬ p424) ∨ (¬ p996)) : p419 ∨ p6 ∨ (¬ p186) ∨ (¬ p134) ∨ (¬ p424) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16919 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)

theorem step32317 (p6 p127 p134 p186 p243 p424 p542 p619 p690 p728 p898 p1098 : Prop)
    (h26839 : p127 ∨ p6)
    (h16920 : (¬ p127) ∨ (¬ p134) ∨ (¬ p186) ∨ (¬ p243) ∨ (¬ p424) ∨ (¬ p542) ∨ (¬ p619) ∨ (¬ p690) ∨ (¬ p728) ∨ (¬ p898) ∨ (¬ p1098)) : (¬ p619) ∨ p6 ∨ (¬ p728) ∨ (¬ p134) ∨ (¬ p186) ∨ (¬ p243) ∨ (¬ p898) ∨ (¬ p690) ∨ (¬ p424) ∨ (¬ p542) ∨ (¬ p1098) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p619 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p728 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p243 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p898 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p1098 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16920 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u11)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u2)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u10)

theorem step32319 (p6 p127 p134 p186 p224 p382 p424 p542 p657 p821 : Prop)
    (h26839 : p127 ∨ p6)
    (h26887 : p657 ∨ p224)
    (h16947 : (¬ p127) ∨ (¬ p134) ∨ (¬ p186) ∨ (¬ p382) ∨ (¬ p424) ∨ (¬ p542) ∨ (¬ p657) ∨ (¬ p821)) : p6 ∨ p224 ∨ (¬ p134) ∨ (¬ p542) ∨ (¬ p186) ∨ (¬ p382) ∨ (¬ p821) ∨ (¬ p424) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p6) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p382 := by
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
  have u8 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16947 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u6)

theorem step32320 (p6 p127 p134 p163 p186 p225 p544 : Prop)
    (h26839 : p127 ∨ p6)
    (h26877 : p544 ∨ p225)
    (h16948 : (¬ p127) ∨ (¬ p134) ∨ (¬ p163) ∨ (¬ p186) ∨ (¬ p544)) : p6 ∨ p225 ∨ (¬ p163) ∨ (¬ p186) ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p6) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16948 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)

theorem step32321 (p6 p8 p127 p134 p186 p224 p243 p422 p710 p1000 p1256 : Prop)
    (h26929 : p1256 ∨ p422)
    (h26889 : p710 ∨ p8)
    (h26839 : p127 ∨ p6)
    (h16953 : (¬ p127) ∨ (¬ p134) ∨ (¬ p186) ∨ (¬ p224) ∨ (¬ p243) ∨ (¬ p710) ∨ (¬ p1000) ∨ (¬ p1256)) : p422 ∨ (¬ p134) ∨ p8 ∨ (¬ p1000) ∨ p6 ∨ (¬ p224) ∨ (¬ p186) ∨ (¬ p243) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p422) := fun hu => hn (Or.inl hu)
  have u1 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p243 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16953 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u8)

theorem step32322 (p6 p8 p127 p134 p186 p224 p243 p424 p710 p1325 : Prop)
    (h26839 : p127 ∨ p6)
    (h26889 : p710 ∨ p8)
    (h16959 : (¬ p127) ∨ (¬ p134) ∨ (¬ p186) ∨ (¬ p224) ∨ (¬ p243) ∨ (¬ p424) ∨ (¬ p710) ∨ (¬ p1325)) : (¬ p424) ∨ (¬ p134) ∨ (¬ p186) ∨ (¬ p224) ∨ (¬ p1325) ∨ (¬ p243) ∨ p6 ∨ p8 := by
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
  have u2 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p243 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h16959 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u4)

theorem step32323 (p6 p127 p134 p186 p422 p980 p983 p1040 p1226 p1256 p1354 : Prop)
    (h26903 : p983 ∨ p980)
    (h26839 : p127 ∨ p6)
    (h26929 : p1256 ∨ p422)
    (h16977 : (¬ p127) ∨ (¬ p134) ∨ (¬ p186) ∨ (¬ p983) ∨ (¬ p1040) ∨ (¬ p1226) ∨ (¬ p1256) ∨ (¬ p1354)) : (¬ p1226) ∨ p980 ∨ (¬ p1354) ∨ (¬ p134) ∨ p6 ∨ p422 ∨ (¬ p1040) ∨ (¬ p186) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1354 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1040 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h16977 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u2)

theorem step32324 (p6 p127 p134 p186 p224 p422 p1001 p1256 : Prop)
    (h26929 : p1256 ∨ p422)
    (h26839 : p127 ∨ p6)
    (h16986 : (¬ p127) ∨ (¬ p134) ∨ (¬ p186) ∨ (¬ p224) ∨ (¬ p1001) ∨ (¬ p1256)) : (¬ p1001) ∨ p422 ∨ (¬ p224) ∨ p6 ∨ (¬ p186) ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1001 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p422) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16986 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u6)

theorem step32326 (p6 p127 p134 p1163 p1226 p1452 : Prop)
    (h26839 : p127 ∨ p6)
    (h18731 : (¬ p127) ∨ (¬ p134) ∨ (¬ p1163) ∨ (¬ p1226) ∨ (¬ p1452)) : (¬ p1163) ∨ (¬ p1452) ∨ p6 ∨ (¬ p134) ∨ (¬ p1226) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18731 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u1)

theorem step32327 (p6 p127 p134 p186 p790 p799 p814 : Prop)
    (h26893 : p814 ∨ p790)
    (h26839 : p127 ∨ p6)
    (h20245 : (¬ p127) ∨ (¬ p134) ∨ (¬ p186) ∨ (¬ p799) ∨ (¬ p814)) : p790 ∨ p6 ∨ (¬ p186) ∨ (¬ p134) ∨ (¬ p799) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p790) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p799 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20245 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)

theorem step32328 (p6 p8 p127 p134 p225 p544 p556 p710 : Prop)
    (h26877 : p544 ∨ p225)
    (h26839 : p127 ∨ p6)
    (h26889 : p710 ∨ p8)
    (h20258 : (¬ p127) ∨ (¬ p134) ∨ (¬ p544) ∨ (¬ p556) ∨ (¬ p710)) : p225 ∨ (¬ p556) ∨ p6 ∨ (¬ p134) ∨ p8 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p225) := fun hu => hn (Or.inl hu)
  have u1 : p556 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20258 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u7)

theorem step32329 (p6 p127 p134 p349 p434 p477 p690 : Prop)
    (h26839 : p127 ∨ p6)
    (h20262 : (¬ p127) ∨ (¬ p134) ∨ (¬ p349) ∨ (¬ p434) ∨ (¬ p477) ∨ (¬ p690)) : (¬ p477) ∨ (¬ p434) ∨ (¬ p690) ∨ p6 ∨ (¬ p134) ∨ (¬ p349) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p477 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20262 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u2)

theorem step32331 (p2 p6 p127 p134 p422 p1256 : Prop)
    (h26839 : p127 ∨ p6)
    (h26929 : p1256 ∨ p422)
    (h17350 : (¬ p2) ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p1256)) : (¬ p2) ∨ (¬ p134) ∨ p6 ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17350 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)

theorem step32332 (p2 p6 p127 p134 p303 p325 : Prop)
    (h26839 : p127 ∨ p6)
    (h18332 : (¬ p2) ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p303) ∨ (¬ p325)) : (¬ p325) ∨ (¬ p2) ∨ (¬ p303) ∨ (¬ p134) ∨ p6 := by
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
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18332 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u0)

theorem step32335 (p6 p14 p68 p127 p134 p225 p229 : Prop)
    (h26839 : p127 ∨ p6)
    (h26849 : p229 ∨ p14)
    (h20257 : (¬ p68) ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p225) ∨ (¬ p229)) : p6 ∨ p14 ∨ (¬ p225) ∨ (¬ p68) ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p6) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p14) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20257 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)

theorem step32336 (p6 p68 p127 p134 p423 p532 p1141 p1208 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26839 : p127 ∨ p6)
    (h20264 : (¬ p68) ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p532) ∨ (¬ p1141) ∨ (¬ p1208)) : (¬ p1208) ∨ p423 ∨ (¬ p134) ∨ (¬ p68) ∨ p6 ∨ (¬ p532) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1208 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p423) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20264 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u0)

theorem step32337 (p6 p68 p127 p134 p185 p237 p980 p983 p1115 p1116 p1473 p1710 : Prop)
    (h26851 : p237 ∨ p185)
    (h26915 : p1116 ∨ p1115)
    (h26839 : p127 ∨ p6)
    (h26903 : p983 ∨ p980)
    (h20267 : (¬ p68) ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p237) ∨ (¬ p983) ∨ (¬ p1116) ∨ (¬ p1473) ∨ (¬ p1710)) : (¬ p1710) ∨ (¬ p134) ∨ p185 ∨ p1115 ∨ p6 ∨ p980 ∨ (¬ p68) ∨ (¬ p1473) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1473 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20267 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u0)

theorem step32338 (p6 p84 p127 p134 p186 p424 p595 p616 p929 p1096 p1195 : Prop)
    (h26883 : p616 ∨ p595)
    (h26839 : p127 ∨ p6)
    (h16923 : (¬ p84) ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p186) ∨ (¬ p424) ∨ (¬ p616) ∨ (¬ p929) ∨ (¬ p1096) ∨ (¬ p1195)) : (¬ p1195) ∨ (¬ p929) ∨ (¬ p1096) ∨ (¬ p134) ∨ (¬ p84) ∨ (¬ p186) ∨ p595 ∨ (¬ p424) ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h16923 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u2)
  · exact False.elim (q8 u0)

theorem step32340 (p6 p8 p127 p134 p836 p1044 p1115 p1116 p1140 p1159 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h26839 : p127 ∨ p6)
    (h26919 : p1159 ∨ p1140)
    (h20260 : (¬ p8) ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p836) ∨ (¬ p1044) ∨ (¬ p1116) ∨ (¬ p1159)) : (¬ p836) ∨ p1115 ∨ (¬ p1044) ∨ p6 ∨ p1140 ∨ (¬ p8) ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1115) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1044 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20260 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u9)

theorem step32341 (p6 p127 p134 p422 p1040 p1074 p1096 p1099 p1256 : Prop)
    (h26929 : p1256 ∨ p422)
    (h26839 : p127 ∨ p6)
    (h26913 : p1099 ∨ p1096)
    (h26172 : (¬ p1099) ∨ (¬ p1040) ∨ (¬ p127) ∨ (¬ p1256) ∨ (¬ p1074) ∨ (¬ p134)) : p422 ∨ (¬ p1074) ∨ (¬ p1040) ∨ p6 ∨ (¬ p134) ∨ p1096 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p422) := fun hu => hn (Or.inl hu)
  have u1 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1040 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26172 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u4)

theorem step32342 (p3 p6 p14 p50 p127 p134 p226 : Prop)
    (h26847 : p226 ∨ p3)
    (h26839 : p127 ∨ p6)
    (h17301 : (¬ p14) ∨ (¬ p50) ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p226)) : p3 ∨ p6 ∨ (¬ p14) ∨ (¬ p134) ∨ (¬ p50) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p50 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17301 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)

theorem step32344 (p3 p6 p104 p127 p134 p226 p726 : Prop)
    (h26847 : p226 ∨ p3)
    (h26839 : p127 ∨ p6)
    (h17253 : (¬ p104) ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p226) ∨ (¬ p726)) : p3 ∨ (¬ p134) ∨ (¬ p104) ∨ (¬ p726) ∨ p6 := by
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
  have u3 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17253 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)

theorem step32345 (p6 p12 p127 p134 p163 p186 : Prop)
    (h26839 : p127 ∨ p6)
    (h16759 : (¬ p12) ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p163) ∨ (¬ p186)) : p6 ∨ (¬ p186) ∨ (¬ p12) ∨ (¬ p163) ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p6) := fun hu => hn (Or.inl hu)
  have u1 : p186 := by
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
  have u4 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h16759 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)

theorem step32346 (p41 p45 p134 p790 p814 p1385 p1393 : Prop)
    (h26893 : p814 ∨ p790)
    (h26933 : p1393 ∨ p1385)
    (h26831 : p45 ∨ p41)
    (h16840 : (¬ p45) ∨ (¬ p134) ∨ (¬ p814) ∨ (¬ p1393)) : p790 ∨ p1385 ∨ (¬ p134) ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p790) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1385) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16840 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step32347 (p41 p45 p90 p101 p134 p224 p789 p790 : Prop)
    (h26586 : p90)
    (h26831 : p45 ∨ p41)
    (h20636 : (¬ p45) ∨ (¬ p90) ∨ (¬ p101) ∨ (¬ p134) ∨ (¬ p224) ∨ (¬ p789) ∨ (¬ p790)) : (¬ p789) ∨ (¬ p101) ∨ (¬ p224) ∨ (¬ p134) ∨ (¬ p790) ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p789 := by
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
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p90 := by
    exact h26586
  have u7 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20636 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u4)

theorem step32348 (p134 p324 p422 p997 p1256 : Prop)
    (h26929 : p1256 ∨ p422)
    (h12190 : (¬ p134) ∨ (¬ p324) ∨ (¬ p997) ∨ (¬ p1256)) : (¬ p324) ∨ (¬ p997) ∨ (¬ p134) ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p324 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p997 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h12190 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)

theorem step32349 (p134 p210 p305 p344 p346 p756 p769 : Prop)
    (h26863 : p346 ∨ p344)
    (h17026 : (¬ p134) ∨ (¬ p210) ∨ (¬ p305) ∨ (¬ p346) ∨ (¬ p756) ∨ (¬ p769)) : (¬ p756) ∨ (¬ p769) ∨ p344 ∨ (¬ p305) ∨ (¬ p134) ∨ (¬ p210) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p769 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17026 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u1)

theorem step32350 (p105 p108 p189 p193 : Prop)
    (h26845 : p193 ∨ p189)
    (h16222 : p105 ∨ (¬ p108) ∨ (¬ p193)) : p105 ∨ p189 ∨ (¬ p108) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p105) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16222 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)

theorem step32369 (p1 p225 p540 p544 : Prop)
    (h26876 : (¬ p225) ∨ (¬ p544))
    (h21065 : p540 ∨ p1 ∨ p544) : p540 ∨ (¬ p225) ∨ p1 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p540) := fun hu => hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : (¬ p544) := by
    rcases h26876 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h21065 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (u3 q2)

theorem step32370 (p225 p540 p544 : Prop)
    (h26876 : (¬ p225) ∨ (¬ p544))
    (h21071 : p540 ∨ p544) : p540 ∨ (¬ p225) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p540) := fun hu => hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p544) := by
    rcases h26876 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h21071 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step32371 (p14 p18 p103 p229 : Prop)
    (h26848 : (¬ p14) ∨ (¬ p229))
    (h14747 : (¬ p18) ∨ (¬ p103) ∨ p229) : (¬ p103) ∨ (¬ p14) ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p229) := by
    rcases h26848 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h14747 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (u3 q2)

theorem step32372 (p15 p69 p161 p1225 p1229 p1325 : Prop)
    (h26925 : p1225 ∨ p161)
    (h26833 : p69 ∨ p15)
    (h20377 : (¬ p69) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1325)) : p161 ∨ (¬ p1229) ∨ p15 ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p161) := fun hu => hn (Or.inl hu)
  have u1 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20377 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)

theorem step32373 (p63 p85 p161 p1225 p1229 p1489 : Prop)
    (h26925 : p1225 ∨ p161)
    (h26835 : p85 ∨ p63)
    (h16384 : (¬ p85) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1489)) : p161 ∨ (¬ p1489) ∨ p63 ∨ (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p161) := fun hu => hn (Or.inl hu)
  have u1 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16384 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)

theorem step32375 (p8 p63 p85 p161 p710 p734 p929 p1102 p1225 p1229 p1335 : Prop)
    (h26925 : p1225 ∨ p161)
    (h26889 : p710 ∨ p8)
    (h26835 : p85 ∨ p63)
    (h16651 : (¬ p85) ∨ (¬ p710) ∨ (¬ p734) ∨ (¬ p929) ∨ (¬ p1102) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1335)) : p161 ∨ (¬ p734) ∨ (¬ p1229) ∨ p8 ∨ (¬ p1102) ∨ p63 ∨ (¬ p1335) ∨ (¬ p929) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p161) := fun hu => hn (Or.inl hu)
  have u1 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h16651 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u6)

theorem step32376 (p63 p85 p161 p980 p1225 p1229 : Prop)
    (h26925 : p1225 ∨ p161)
    (h26835 : p85 ∨ p63)
    (h16576 : (¬ p85) ∨ (¬ p980) ∨ (¬ p1225) ∨ (¬ p1229)) : p161 ∨ (¬ p980) ∨ p63 ∨ (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p161) := fun hu => hn (Or.inl hu)
  have u1 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16576 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)

theorem step32377 (p16 p161 p189 p424 p435 p796 p1225 p1229 p1335 : Prop)
    (h26891 : p796 ∨ p424)
    (h26925 : p1225 ∨ p161)
    (h19851 : (¬ p16) ∨ (¬ p189) ∨ (¬ p435) ∨ (¬ p796) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1335)) : p424 ∨ p161 ∨ (¬ p435) ∨ (¬ p1335) ∨ (¬ p1229) ∨ (¬ p16) ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p161) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19851 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u3)

theorem step32381 (p12 p63 p85 p104 p161 p344 p346 p929 p1074 p1225 p1229 : Prop)
    (h26925 : p1225 ∨ p161)
    (h26835 : p85 ∨ p63)
    (h26863 : p346 ∨ p344)
    (h16670 : (¬ p12) ∨ (¬ p85) ∨ (¬ p104) ∨ (¬ p346) ∨ (¬ p929) ∨ (¬ p1074) ∨ (¬ p1225) ∨ (¬ p1229)) : p161 ∨ (¬ p929) ∨ (¬ p12) ∨ (¬ p1074) ∨ p63 ∨ (¬ p1229) ∨ p344 ∨ (¬ p104) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p161) := fun hu => hn (Or.inl hu)
  have u1 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h16670 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u5)

theorem step32384 (p5 p6 p10 p161 p438 p1225 p1229 p1335 : Prop)
    (h26925 : p1225 ∨ p161)
    (h18351 : (¬ p5) ∨ (¬ p6) ∨ (¬ p10) ∨ (¬ p438) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1335)) : (¬ p438) ∨ (¬ p10) ∨ p161 ∨ (¬ p1229) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p1335) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p161) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18351 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step32386 (p63 p161 p1225 p1226 p1230 p1270 : Prop)
    (h26925 : p1225 ∨ p161)
    (h18163 : (¬ p63) ∨ (¬ p1225) ∨ (¬ p1226) ∨ (¬ p1230) ∨ (¬ p1270)) : (¬ p1270) ∨ p161 ∨ (¬ p1226) ∨ (¬ p1230) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1270 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p161) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1230 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18163 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u0)

theorem step32388 (p3 p38 p49 p63 p85 p161 p226 p940 p985 p1225 p1229 : Prop)
    (h26835 : p85 ∨ p63)
    (h26925 : p1225 ∨ p161)
    (h26847 : p226 ∨ p3)
    (h16693 : (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p226) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1225) ∨ (¬ p1229)) : (¬ p940) ∨ p63 ∨ (¬ p985) ∨ p161 ∨ p3 ∨ (¬ p49) ∨ (¬ p1229) ∨ (¬ p38) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p63) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p161) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16693 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u6)

theorem step32389 (p161 p462 p532 p633 p636 p1084 p1225 : Prop)
    (h26925 : p1225 ∨ p161)
    (h26885 : p636 ∨ p633)
    (h17009 : (¬ p462) ∨ (¬ p532) ∨ (¬ p636) ∨ (¬ p1084) ∨ (¬ p1225)) : p161 ∨ p633 ∨ (¬ p462) ∨ (¬ p1084) ∨ (¬ p532) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p161) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p633) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p462 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17009 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)

theorem step32390 (p2 p18 p161 p209 p234 p532 p961 p1225 : Prop)
    (h26925 : p1225 ∨ p161)
    (h16899 : (¬ p2) ∨ (¬ p18) ∨ (¬ p209) ∨ (¬ p234) ∨ (¬ p532) ∨ (¬ p961) ∨ (¬ p1225)) : (¬ p2) ∨ (¬ p234) ∨ (¬ p209) ∨ (¬ p532) ∨ (¬ p961) ∨ p161 ∨ (¬ p18) := by
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
  have u2 : p209 := by
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
  have u5 : (¬ p161) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h16899 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u7)

theorem step32398 (p423 p1141 p1147 p1154 p1155 p1156 p1157 p1158 : Prop)
    (h26916 : (¬ p423) ∨ (¬ p1141))
    (h6802 : p1141 ∨ p1147 ∨ (¬ p1154) ∨ (¬ p1155) ∨ (¬ p1156) ∨ (¬ p1157) ∨ (¬ p1158)) : p1147 ∨ (¬ p1157) ∨ (¬ p423) ∨ (¬ p1154) ∨ (¬ p1155) ∨ (¬ p1156) ∨ (¬ p1158) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1147) := fun hu => hn (Or.inl hu)
  have u1 : p1157 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1154 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1155 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p1141) := by
    rcases h26916 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h6802 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u7 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u6)

theorem step32399 (p423 p1141 p1148 p1154 p1155 p1156 p1157 p1158 : Prop)
    (h26916 : (¬ p423) ∨ (¬ p1141))
    (h6803 : p1141 ∨ p1148 ∨ (¬ p1154) ∨ (¬ p1155) ∨ (¬ p1156) ∨ (¬ p1157) ∨ (¬ p1158)) : p1148 ∨ (¬ p1157) ∨ (¬ p423) ∨ (¬ p1154) ∨ (¬ p1155) ∨ (¬ p1156) ∨ (¬ p1158) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1148) := fun hu => hn (Or.inl hu)
  have u1 : p1157 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1154 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1155 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p1141) := by
    rcases h26916 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h6803 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u7 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u6)

theorem step32401 (p121 p143 p532 p1206 p1496 p1508 : Prop)
    (h26923 : p1206 ∨ p121)
    (h20543 : (¬ p143) ∨ (¬ p532) ∨ (¬ p1206) ∨ (¬ p1496) ∨ (¬ p1508)) : (¬ p1496) ∨ p121 ∨ (¬ p143) ∨ (¬ p1508) ∨ (¬ p532) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p121) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p143 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20543 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u3)

theorem step32406 (p86 p228 p532 p595 p616 p1287 p1346 p1508 : Prop)
    (h26883 : p616 ∨ p595)
    (h16930 : (¬ p86) ∨ (¬ p228) ∨ (¬ p532) ∨ (¬ p616) ∨ (¬ p1287) ∨ (¬ p1346) ∨ (¬ p1508)) : (¬ p1346) ∨ (¬ p1508) ∨ (¬ p228) ∨ (¬ p532) ∨ (¬ p1287) ∨ p595 ∨ (¬ p86) := by
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
  have u2 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h16930 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u1)

theorem step32408 (p84 p495 p499 p582 p1229 p1232 p1295 p1325 p1346 p1508 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h26875 : p499 ∨ p495)
    (h20276 : (¬ p84) ∨ (¬ p499) ∨ (¬ p582) ∨ (¬ p1232) ∨ (¬ p1295) ∨ (¬ p1325) ∨ (¬ p1346) ∨ (¬ p1508)) : (¬ p1295) ∨ p1229 ∨ (¬ p1325) ∨ (¬ p1508) ∨ (¬ p582) ∨ p495 ∨ (¬ p84) ∨ (¬ p1346) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1295 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20276 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u3)

theorem step32409 (p185 p237 p918 p1273 p1508 : Prop)
    (h26851 : p237 ∨ p185)
    (h20624 : (¬ p237) ∨ (¬ p918) ∨ (¬ p1273) ∨ (¬ p1508)) : p185 ∨ (¬ p918) ∨ (¬ p1508) ∨ (¬ p1273) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p185) := fun hu => hn (Or.inl hu)
  have u1 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h20624 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)

theorem step32412 (p134 p161 p1229 p1232 p1250 p1508 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h16888 : (¬ p134) ∨ (¬ p161) ∨ (¬ p1232) ∨ (¬ p1250) ∨ (¬ p1508)) : (¬ p1250) ∨ (¬ p1508) ∨ (¬ p161) ∨ (¬ p134) ∨ p1229 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1250 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16888 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)

theorem step32413 (p41 p45 p980 p1273 p1508 : Prop)
    (h26831 : p45 ∨ p41)
    (h19254 : (¬ p45) ∨ (¬ p980) ∨ (¬ p1273) ∨ (¬ p1508)) : (¬ p1273) ∨ (¬ p1508) ∨ p41 ∨ (¬ p980) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19254 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)

theorem step32414 (p41 p45 p1273 p1325 p1508 : Prop)
    (h26831 : p45 ∨ p41)
    (h20155 : (¬ p45) ∨ (¬ p1273) ∨ (¬ p1325) ∨ (¬ p1508)) : (¬ p1273) ∨ (¬ p1508) ∨ p41 ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20155 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)

theorem step32415 (p790 p814 p1325 p1346 p1508 : Prop)
    (h26893 : p814 ∨ p790)
    (h18392 : (¬ p814) ∨ (¬ p1325) ∨ (¬ p1346) ∨ (¬ p1508)) : (¬ p1346) ∨ (¬ p1508) ∨ (¬ p1325) ∨ p790 := by
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
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18392 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)

theorem step32416 (p89 p124 p189 p193 p633 p636 p961 p1210 p1250 p1465 p1508 : Prop)
    (h26845 : p193 ∨ p189)
    (h26885 : p636 ∨ p633)
    (h18556 : (¬ p89) ∨ (¬ p124) ∨ (¬ p193) ∨ (¬ p636) ∨ (¬ p961) ∨ (¬ p1210) ∨ (¬ p1250) ∨ (¬ p1465) ∨ (¬ p1508)) : (¬ p961) ∨ (¬ p1210) ∨ (¬ p1250) ∨ (¬ p1508) ∨ p189 ∨ (¬ p89) ∨ p633 ∨ (¬ p1465) ∨ (¬ p124) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1250 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p633) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18556 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u3)

theorem step32417 (p12 p560 p1036 p1055 : Prop)
    (h26906 : (¬ p12) ∨ (¬ p1036))
    (h11753 : (¬ p560) ∨ p1036 ∨ (¬ p1055)) : (¬ p1055) ∨ (¬ p12) ∨ (¬ p560) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1036) := by
    rcases h26906 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h11753 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u0)

theorem step32418 (p63 p980 p1022 p1055 p1103 p1330 p1385 p1393 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h19386 : (¬ p63) ∨ (¬ p980) ∨ (¬ p1022) ∨ (¬ p1055) ∨ (¬ p1103) ∨ (¬ p1330) ∨ (¬ p1393)) : (¬ p1022) ∨ (¬ p1103) ∨ p1385 ∨ (¬ p1330) ∨ (¬ p980) ∨ (¬ p1055) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1330 := by
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
  have u6 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19386 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step32419 (p63 p85 p929 p980 p1055 p1102 p1229 p1291 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26835 : p85 ∨ p63)
    (h16725 : (¬ p85) ∨ (¬ p929) ∨ (¬ p980) ∨ (¬ p1055) ∨ (¬ p1102) ∨ (¬ p1229) ∨ (¬ p1291) ∨ (¬ p1333)) : (¬ p1229) ∨ p1325 ∨ (¬ p1102) ∨ (¬ p980) ∨ (¬ p929) ∨ (¬ p1055) ∨ p63 ∨ (¬ p1291) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1291 := by
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
    · exact False.elim (u6 q1)
  rcases h16725 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u8)

theorem step32421 (p664 p836 p840 p980 p983 p1489 : Prop)
    (h26903 : p983 ∨ p980)
    (h26895 : p840 ∨ p836)
    (h23684 : (¬ p1489) ∨ (¬ p983) ∨ (¬ p840) ∨ (¬ p664)) : (¬ p1489) ∨ p980 ∨ (¬ p664) ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h23684 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)

theorem step32446 (p234 p1187 p1195 p1196 p1197 p1198 p1199 p1200 : Prop)
    (h26920 : (¬ p234) ∨ (¬ p1187))
    (h7077 : p1187 ∨ p1195 ∨ (¬ p1196) ∨ (¬ p1197) ∨ (¬ p1198) ∨ (¬ p1199) ∨ (¬ p1200)) : p1195 ∨ (¬ p1196) ∨ (¬ p234) ∨ (¬ p1199) ∨ (¬ p1200) ∨ (¬ p1197) ∨ (¬ p1198) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1195) := fun hu => hn (Or.inl hu)
  have u1 : p1196 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1199 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1200 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1197 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1198 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p1187) := by
    rcases h26920 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h7077 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u7 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)

theorem step32450 (p63 p85 p1385 p1387 p1394 : Prop)
    (h26835 : p85 ∨ p63)
    (h21028 : p1394 ∨ (¬ p1385) ∨ (¬ p1387) ∨ (¬ p85)) : p1394 ∨ p63 ∨ (¬ p1385) ∨ (¬ p1387) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1394) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p63) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h21028 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step32452 (p18 p63 p85 p234 p789 p858 p1366 p1385 : Prop)
    (h26897 : p858 ∨ p789)
    (h26835 : p85 ∨ p63)
    (h26189 : (¬ p1366) ∨ (¬ p858) ∨ (¬ p234) ∨ (¬ p1385) ∨ (¬ p85) ∨ (¬ p18)) : (¬ p1366) ∨ p789 ∨ (¬ p18) ∨ p63 ∨ (¬ p234) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p789) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h26189 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)

theorem step32453 (p6 p63 p85 p121 p127 p228 p789 p858 p1385 : Prop)
    (h26839 : p127 ∨ p6)
    (h26897 : p858 ∨ p789)
    (h26835 : p85 ∨ p63)
    (h26190 : (¬ p1385) ∨ (¬ p858) ∨ (¬ p85) ∨ (¬ p127) ∨ (¬ p121) ∨ (¬ p228)) : p6 ∨ p789 ∨ p63 ∨ (¬ p228) ∨ (¬ p1385) ∨ (¬ p121) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p6) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p789) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h26190 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u3)

theorem step32454 (p124 p262 p515 p576 p581 p1385 : Prop)
    (h26879 : p581 ∨ p576)
    (h24221 : (¬ p515) ∨ (¬ p1385) ∨ (¬ p124) ∨ (¬ p581) ∨ (¬ p262)) : (¬ p515) ∨ (¬ p1385) ∨ (¬ p262) ∨ (¬ p124) ∨ p576 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p515 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h24221 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)

theorem step32455 (p63 p85 p728 p1015 p1385 : Prop)
    (h26835 : p85 ∨ p63)
    (h19428 : (¬ p85) ∨ (¬ p728) ∨ (¬ p1015) ∨ (¬ p1385)) : (¬ p1015) ∨ (¬ p728) ∨ p63 ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19428 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)

theorem step32456 (p90 p687 p820 p1015 p1385 : Prop)
    (h26586 : p90)
    (h18478 : (¬ p90) ∨ (¬ p687) ∨ (¬ p820) ∨ (¬ p1015) ∨ (¬ p1385)) : (¬ p1015) ∨ (¬ p687) ∨ (¬ p1385) ∨ (¬ p820) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p820 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p90 := by
    exact h26586
  rcases h18478 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u2)

theorem step32457 (p18 p89 p124 p210 p304 p790 p1076 p1120 p1273 p1385 : Prop)
    (h26859 : p304 ∨ p124)
    (h20598 : (¬ p18) ∨ (¬ p89) ∨ (¬ p210) ∨ (¬ p304) ∨ (¬ p790) ∨ (¬ p1076) ∨ (¬ p1120) ∨ (¬ p1273) ∨ (¬ p1385)) : (¬ p210) ∨ p124 ∨ (¬ p1273) ∨ (¬ p89) ∨ (¬ p1385) ∨ (¬ p1120) ∨ (¬ p1076) ∨ (¬ p790) ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1120 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20598 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u2)
  · exact False.elim (q8 u4)

theorem step32458 (p17 p90 p256 p382 p574 p633 p665 p819 p1076 p1077 p1385 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26586 : p90)
    (h26853 : p256 ∨ p17)
    (h18043 : (¬ p90) ∨ (¬ p256) ∨ (¬ p382) ∨ (¬ p574) ∨ (¬ p633) ∨ (¬ p665) ∨ (¬ p819) ∨ (¬ p1077) ∨ (¬ p1385)) : (¬ p819) ∨ p1076 ∨ (¬ p665) ∨ (¬ p574) ∨ (¬ p633) ∨ (¬ p1385) ∨ p17 ∨ (¬ p382) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p819 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p665 := by
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
  have u5 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p90 := by
    exact h26586
  have u10 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18043 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u5)

theorem step32459 (p17 p90 p256 p574 p633 p665 p789 p858 p1076 p1077 p1385 : Prop)
    (h26853 : p256 ∨ p17)
    (h26586 : p90)
    (h26911 : p1077 ∨ p1076)
    (h26897 : p858 ∨ p789)
    (h18048 : (¬ p90) ∨ (¬ p256) ∨ (¬ p574) ∨ (¬ p633) ∨ (¬ p665) ∨ (¬ p858) ∨ (¬ p1077) ∨ (¬ p1385)) : (¬ p1385) ∨ p17 ∨ (¬ p633) ∨ p1076 ∨ p789 ∨ (¬ p665) ∨ (¬ p574) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p574 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p90 := by
    exact h26586
  have u9 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18048 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u0)

theorem step32461 (p382 p576 p581 p819 p1325 p1385 : Prop)
    (h26879 : p581 ∨ p576)
    (h19218 : (¬ p382) ∨ (¬ p581) ∨ (¬ p819) ∨ (¬ p1325) ∨ (¬ p1385)) : (¬ p1385) ∨ (¬ p819) ∨ (¬ p382) ∨ p576 ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p819 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19218 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u0)

theorem step32463 (p63 p85 p303 p349 p387 p789 p858 p1385 : Prop)
    (h26867 : p387 ∨ p303)
    (h26835 : p85 ∨ p63)
    (h26897 : p858 ∨ p789)
    (h19274 : (¬ p85) ∨ (¬ p349) ∨ (¬ p387) ∨ (¬ p858) ∨ (¬ p1385)) : p303 ∨ (¬ p1385) ∨ (¬ p349) ∨ p63 ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19274 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u1)

theorem step32464 (p63 p85 p789 p858 p1325 p1385 : Prop)
    (h26897 : p858 ∨ p789)
    (h26835 : p85 ∨ p63)
    (h16843 : (¬ p85) ∨ (¬ p858) ∨ (¬ p1325) ∨ (¬ p1385)) : p789 ∨ p63 ∨ (¬ p1385) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p789) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p63) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16843 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)

theorem step32465 (p63 p85 p224 p657 p789 p858 p1385 : Prop)
    (h26887 : p657 ∨ p224)
    (h26835 : p85 ∨ p63)
    (h26897 : p858 ∨ p789)
    (h17063 : (¬ p85) ∨ (¬ p657) ∨ (¬ p858) ∨ (¬ p1385)) : p224 ∨ (¬ p1385) ∨ p63 ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p224) := fun hu => hn (Or.inl hu)
  have u1 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17063 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)

theorem step32466 (p5 p6 p89 p121 p185 p237 p918 p1206 p1273 p1490 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26851 : p237 ∨ p185)
    (h20646 : (¬ p5) ∨ (¬ p6) ∨ (¬ p89) ∨ (¬ p237) ∨ (¬ p918) ∨ (¬ p1206) ∨ (¬ p1273) ∨ (¬ p1490)) : p121 ∨ (¬ p5) ∨ (¬ p918) ∨ (¬ p1273) ∨ p185 ∨ (¬ p1490) ∨ (¬ p6) ∨ (¬ p89) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1490 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20646 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u5)

theorem step32467 (p63 p124 p134 p210 p304 p726 p985 p1273 p1508 : Prop)
    (h26859 : p304 ∨ p124)
    (h20384 : (¬ p63) ∨ (¬ p134) ∨ (¬ p210) ∨ (¬ p304) ∨ (¬ p726) ∨ (¬ p985) ∨ (¬ p1273) ∨ (¬ p1508)) : p124 ∨ (¬ p726) ∨ (¬ p985) ∨ (¬ p210) ∨ (¬ p63) ∨ (¬ p134) ∨ (¬ p1273) ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p134 := by
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
  have u8 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h20384 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u7)

theorem step32468 (p5 p10 p63 p121 p125 p206 p323 p1206 p1273 p1490 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26861 : p323 ∨ p10)
    (h18330 : (¬ p5) ∨ (¬ p63) ∨ (¬ p125) ∨ (¬ p206) ∨ (¬ p323) ∨ (¬ p1206) ∨ (¬ p1273) ∨ (¬ p1490)) : p121 ∨ (¬ p125) ∨ (¬ p63) ∨ (¬ p1490) ∨ (¬ p1273) ∨ (¬ p5) ∨ p10 ∨ (¬ p206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1490 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p206 := by
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
    · exact False.elim (u6 q1)
  rcases h18330 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u3)

theorem step32469 (p121 p258 p576 p1206 p1273 p1495 : Prop)
    (h26923 : p1206 ∨ p121)
    (h18524 : (¬ p258) ∨ (¬ p576) ∨ (¬ p1206) ∨ (¬ p1273) ∨ (¬ p1495)) : (¬ p258) ∨ p121 ∨ (¬ p576) ∨ (¬ p1273) ∨ (¬ p1495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p121) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p576 := by
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
  have u5 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18524 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)

theorem step32470 (p15 p44 p63 p69 p1257 p1273 : Prop)
    (h26833 : p69 ∨ p15)
    (h17755 : (¬ p44) ∨ (¬ p63) ∨ (¬ p69) ∨ (¬ p1257) ∨ (¬ p1273)) : (¬ p1257) ∨ p15 ∨ (¬ p63) ∨ (¬ p44) ∨ (¬ p1273) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1257 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17755 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)

theorem step32472 (p862 p1273 p1385 p1393 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h16040 : (¬ p862) ∨ p1273 ∨ (¬ p1393)) : (¬ p862) ∨ p1385 ∨ p1273 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p862 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1385) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1273) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16040 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)

theorem step32475 (p790 p814 p861 p1325 p1333 p1346 p1385 p1393 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h26893 : p814 ∨ p790)
    (h26931 : p1333 ∨ p1325)
    (h18414 : (¬ p814) ∨ (¬ p861) ∨ (¬ p1333) ∨ (¬ p1346) ∨ (¬ p1393)) : (¬ p861) ∨ p1385 ∨ (¬ p1346) ∨ p790 ∨ p1325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p861 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1385) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18414 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step32476 (p63 p789 p1325 p1333 p1385 p1393 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26933 : p1393 ∨ p1385)
    (h18486 : (¬ p63) ∨ (¬ p789) ∨ (¬ p1333) ∨ (¬ p1393)) : p1325 ∨ (¬ p789) ∨ p1385 ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1325) := fun hu => hn (Or.inl hu)
  have u1 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18486 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step32477 (p63 p862 p1325 p1385 p1393 p1508 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h19384 : (¬ p63) ∨ (¬ p862) ∨ (¬ p1325) ∨ (¬ p1393) ∨ (¬ p1508)) : (¬ p862) ∨ p1385 ∨ (¬ p63) ∨ (¬ p1508) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p862 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1385) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19384 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)

theorem step32478 (p3 p5 p89 p225 p226 p838 p1249 p1346 p1385 p1393 : Prop)
    (h26847 : p226 ∨ p3)
    (h26933 : p1393 ∨ p1385)
    (h18370 : (¬ p5) ∨ (¬ p89) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p838) ∨ (¬ p1249) ∨ (¬ p1346) ∨ (¬ p1393)) : p3 ∨ (¬ p1346) ∨ (¬ p1249) ∨ (¬ p838) ∨ (¬ p225) ∨ (¬ p89) ∨ p1385 ∨ (¬ p5) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p838 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18370 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u9)

theorem step32480 (p41 p45 p690 p1022 p1385 p1393 : Prop)
    (h26831 : p45 ∨ p41)
    (h26933 : p1393 ∨ p1385)
    (h19029 : (¬ p45) ∨ (¬ p690) ∨ (¬ p1022) ∨ (¬ p1393)) : (¬ p1022) ∨ (¬ p690) ∨ p41 ∨ p1385 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19029 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)

theorem step32481 (p18 p63 p210 p389 p789 p959 p1226 p1385 p1393 p1452 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h20632 : (¬ p18) ∨ (¬ p63) ∨ (¬ p210) ∨ (¬ p389) ∨ (¬ p789) ∨ (¬ p959) ∨ (¬ p1226) ∨ (¬ p1393) ∨ (¬ p1452)) : (¬ p789) ∨ (¬ p1452) ∨ p1385 ∨ (¬ p959) ∨ (¬ p210) ∨ (¬ p1226) ∨ (¬ p18) ∨ (¬ p63) ∨ (¬ p389) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p959 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20632 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u1)

theorem step32482 (p125 p303 p980 p983 p1325 : Prop)
    (h26903 : p983 ∨ p980)
    (h18738 : (¬ p125) ∨ (¬ p303) ∨ (¬ p983) ∨ (¬ p1325)) : p980 ∨ (¬ p125) ∨ (¬ p1325) ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h18738 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)

theorem step32483 (p14 p15 p125 p225 p303 p544 p1325 : Prop)
    (h26877 : p544 ∨ p225)
    (h26193 : (¬ p1325) ∨ (¬ p125) ∨ (¬ p303) ∨ (¬ p15) ∨ (¬ p14) ∨ (¬ p544)) : (¬ p15) ∨ (¬ p125) ∨ (¬ p303) ∨ (¬ p1325) ∨ (¬ p14) ∨ p225 := by
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
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26193 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)

theorem step32484 (p125 p189 p193 p267 p303 p1325 p1469 p1713 : Prop)
    (h26845 : p193 ∨ p189)
    (h18740 : (¬ p125) ∨ (¬ p193) ∨ (¬ p267) ∨ (¬ p303) ∨ (¬ p1325) ∨ (¬ p1469) ∨ (¬ p1713)) : (¬ p1713) ∨ (¬ p125) ∨ p189 ∨ (¬ p267) ∨ (¬ p1325) ∨ (¬ p1469) ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1713 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p267 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1469 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18740 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u0)

theorem step32485 (p125 p189 p193 p267 p422 p438 p1035 p1256 p1335 : Prop)
    (h26929 : p1256 ∨ p422)
    (h26845 : p193 ∨ p189)
    (h18763 : (¬ p125) ∨ (¬ p193) ∨ (¬ p267) ∨ (¬ p438) ∨ (¬ p1035) ∨ (¬ p1256) ∨ (¬ p1335)) : p422 ∨ (¬ p125) ∨ p189 ∨ (¬ p267) ∨ (¬ p1335) ∨ (¬ p1035) ∨ (¬ p438) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p422) := fun hu => hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p267 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18763 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u4)

theorem step32486 (p125 p163 p189 p193 p225 p267 p381 p532 p544 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26877 : p544 ∨ p225)
    (h26845 : p193 ∨ p189)
    (h18749 : (¬ p125) ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p267) ∨ (¬ p381) ∨ (¬ p532) ∨ (¬ p544) ∨ (¬ p1333)) : (¬ p125) ∨ p1325 ∨ (¬ p532) ∨ p225 ∨ p189 ∨ (¬ p267) ∨ (¬ p163) ∨ (¬ p381) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p267 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p381 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18749 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u8)

theorem step32487 (p3 p14 p125 p226 p420 p455 p456 p494 p601 p1140 p1210 : Prop)
    (h26847 : p226 ∨ p3)
    (h26881 : p601 ∨ p420)
    (h26871 : p456 ∨ p455)
    (h17318 : (¬ p14) ∨ (¬ p125) ∨ (¬ p226) ∨ (¬ p456) ∨ (¬ p494) ∨ (¬ p601) ∨ (¬ p1140) ∨ (¬ p1210)) : (¬ p1210) ∨ p3 ∨ (¬ p125) ∨ (¬ p494) ∨ (¬ p1140) ∨ (¬ p14) ∨ p420 ∨ p455 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p455) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h17318 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u0)

theorem step32488 (p41 p45 p160 p420 p438 p495 p1273 p1335 p1348 : Prop)
    (h26831 : p45 ∨ p41)
    (h20071 : (¬ p45) ∨ (¬ p160) ∨ (¬ p420) ∨ (¬ p438) ∨ (¬ p495) ∨ (¬ p1273) ∨ (¬ p1335) ∨ (¬ p1348)) : (¬ p420) ∨ (¬ p160) ∨ p41 ∨ (¬ p438) ∨ (¬ p1348) ∨ (¬ p1273) ∨ (¬ p495) ∨ (¬ p1335) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20071 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step32491 (p980 p983 p1095 p1096 p1325 : Prop)
    (h26903 : p983 ∨ p980)
    (h17518 : (¬ p983) ∨ (¬ p1095) ∨ (¬ p1096) ∨ (¬ p1325)) : p980 ∨ (¬ p1096) ∨ (¬ p1325) ∨ (¬ p1095) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17518 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)

theorem step32493 (p595 p616 p728 p1096 p1545 : Prop)
    (h26883 : p616 ∨ p595)
    (h16711 : (¬ p616) ∨ (¬ p728) ∨ (¬ p1096) ∨ (¬ p1545)) : (¬ p1545) ∨ (¬ p1096) ∨ p595 ∨ (¬ p728) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16711 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)

theorem step32494 (p106 p883 p1076 p1077 p1096 p1229 p1232 p1307 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h26911 : p1077 ∨ p1076)
    (h17834 : (¬ p106) ∨ (¬ p883) ∨ (¬ p1077) ∨ (¬ p1096) ∨ (¬ p1232) ∨ (¬ p1307)) : p1229 ∨ (¬ p1096) ∨ (¬ p1307) ∨ (¬ p106) ∨ (¬ p883) ∨ p1076 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1229) := fun hu => hn (Or.inl hu)
  have u1 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1307 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p883 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17834 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)

theorem step32496 (p21 p121 p495 p639 p1080 p1096 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h16380 : (¬ p21) ∨ (¬ p495) ∨ (¬ p639) ∨ (¬ p1080) ∨ (¬ p1096) ∨ (¬ p1206)) : p121 ∨ (¬ p1080) ∨ (¬ p1096) ∨ (¬ p21) ∨ (¬ p495) ∨ (¬ p639) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p1080 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p21 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p639 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h16380 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)

theorem step32497 (p15 p50 p69 p163 p167 p883 p1096 : Prop)
    (h26843 : p167 ∨ p163)
    (h26833 : p69 ∨ p15)
    (h16787 : (¬ p50) ∨ (¬ p69) ∨ (¬ p167) ∨ (¬ p883) ∨ (¬ p1096)) : (¬ p1096) ∨ p163 ∨ p15 ∨ (¬ p883) ∨ (¬ p50) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p883 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p50 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16787 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u0)

theorem step32498 (p15 p69 p225 p544 p728 p883 p1096 : Prop)
    (h26877 : p544 ∨ p225)
    (h26833 : p69 ∨ p15)
    (h16781 : (¬ p69) ∨ (¬ p544) ∨ (¬ p728) ∨ (¬ p883) ∨ (¬ p1096)) : p225 ∨ (¬ p883) ∨ p15 ∨ (¬ p1096) ∨ (¬ p728) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p225) := fun hu => hn (Or.inl hu)
  have u1 : p883 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16781 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)

theorem step32499 (p15 p69 p225 p344 p346 p544 p883 p1096 : Prop)
    (h26877 : p544 ∨ p225)
    (h26863 : p346 ∨ p344)
    (h26833 : p69 ∨ p15)
    (h19319 : (¬ p69) ∨ (¬ p346) ∨ (¬ p544) ∨ (¬ p883) ∨ (¬ p1096)) : p225 ∨ (¬ p883) ∨ p344 ∨ (¬ p1096) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p225) := fun hu => hn (Or.inl hu)
  have u1 : p883 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19319 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)

theorem step32545 (p633 p636 p641 p643 p644 p645 p646 p647 : Prop)
    (h26884 : (¬ p633) ∨ (¬ p636))
    (h3629 : p636 ∨ p641 ∨ (¬ p643) ∨ (¬ p644) ∨ (¬ p645) ∨ (¬ p646) ∨ (¬ p647)) : p641 ∨ (¬ p645) ∨ (¬ p633) ∨ (¬ p646) ∨ (¬ p643) ∨ (¬ p644) ∨ (¬ p647) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p641) := fun hu => hn (Or.inl hu)
  have u1 : p645 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p646 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p643 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p644 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p647 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p636) := by
    rcases h26884 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h3629 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u7 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step32546 (p8 p261 p305 p344 p710 p980 p1076 : Prop)
    (h26889 : p710 ∨ p8)
    (h20060 : (¬ p261) ∨ (¬ p305) ∨ (¬ p344) ∨ (¬ p710) ∨ (¬ p980) ∨ (¬ p1076)) : (¬ p305) ∨ (¬ p344) ∨ (¬ p1076) ∨ p8 ∨ (¬ p261) ∨ (¬ p980) := by
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
  have u2 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20060 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u2)

theorem step32548 (p1076 p1077 p1080 : Prop)
    (h26910 : (¬ p1076) ∨ (¬ p1077))
    (h20949 : p1080 ∨ p1077) : p1080 ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1080) := fun hu => hn (Or.inl hu)
  have u1 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1077) := by
    rcases h26910 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h20949 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step32549 (p224 p657 p664 : Prop)
    (h26886 : (¬ p224) ∨ (¬ p657))
    (h22831 : p664 ∨ p657) : p664 ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p664) := fun hu => hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p657) := by
    rcases h26886 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h22831 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step32553 (p3 p5 p63 p226 p940 p985 p1273 p1508 : Prop)
    (h26847 : p226 ∨ p3)
    (h18078 : (¬ p5) ∨ (¬ p63) ∨ (¬ p226) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1273) ∨ (¬ p1508)) : (¬ p940) ∨ p3 ∨ (¬ p985) ∨ (¬ p63) ∨ (¬ p5) ∨ (¬ p1273) ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p5 := by
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
  have u7 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18078 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)

theorem step32556 (p14 p15 p69 p86 p229 p940 p985 p1346 p1508 : Prop)
    (h26849 : p229 ∨ p14)
    (h26833 : p69 ∨ p15)
    (h18986 : (¬ p69) ∨ (¬ p86) ∨ (¬ p229) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1346) ∨ (¬ p1508)) : (¬ p940) ∨ p14 ∨ (¬ p1346) ∨ (¬ p86) ∨ p15 ∨ (¬ p985) ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p14) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18986 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u6)

theorem step32557 (p14 p158 p170 p229 p536 p940 : Prop)
    (h26849 : p229 ∨ p14)
    (h26194 : (¬ p940) ∨ (¬ p536) ∨ (¬ p158) ∨ (¬ p170) ∨ (¬ p229)) : (¬ p940) ∨ (¬ p536) ∨ p14 ∨ (¬ p170) ∨ (¬ p158) := by
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
  have u2 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p170 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h26194 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)

theorem step32558 (p3 p6 p127 p226 p756 p940 : Prop)
    (h26839 : p127 ∨ p6)
    (h26847 : p226 ∨ p3)
    (h17344 : (¬ p127) ∨ (¬ p226) ∨ (¬ p756) ∨ (¬ p940)) : (¬ p940) ∨ (¬ p756) ∨ p6 ∨ p3 := by
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
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17344 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)

theorem step32581 (p63 p224 p897 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h19049 : (¬ p63) ∨ (¬ p224) ∨ (¬ p897) ∨ (¬ p1099)) : p1096 ∨ (¬ p897) ∨ (¬ p63) ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1096) := fun hu => hn (Or.inl hu)
  have u1 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19049 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)

theorem step32583 (p63 p344 p897 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h20468 : (¬ p63) ∨ (¬ p344) ∨ (¬ p897) ∨ (¬ p1099)) : p1096 ∨ (¬ p344) ∨ (¬ p897) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1096) := fun hu => hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p897 := by
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
  rcases h20468 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step32584 (p86 p303 p347 p789 p790 p897 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h17033 : (¬ p86) ∨ (¬ p303) ∨ (¬ p347) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p897) ∨ (¬ p1099)) : (¬ p789) ∨ (¬ p790) ∨ (¬ p86) ∨ p1096 ∨ (¬ p897) ∨ (¬ p303) ∨ (¬ p347) := by
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
  have u2 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17033 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u7)

theorem step32585 (p17 p86 p256 p303 p347 p519 p789 p897 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26853 : p256 ∨ p17)
    (h16971 : (¬ p86) ∨ (¬ p256) ∨ (¬ p303) ∨ (¬ p347) ∨ (¬ p519) ∨ (¬ p789) ∨ (¬ p897) ∨ (¬ p1099)) : (¬ p789) ∨ (¬ p303) ∨ p1096 ∨ (¬ p519) ∨ p17 ∨ (¬ p347) ∨ (¬ p86) ∨ (¬ p897) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p519 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p86 := by
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
    · exact False.elim (u2 q1)
  have u9 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16971 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u8)

theorem step32586 (p225 p544 p883 p897 : Prop)
    (h26877 : p544 ∨ p225)
    (h5200 : (¬ p544) ∨ (¬ p883) ∨ (¬ p897)) : (¬ p883) ∨ (¬ p897) ∨ p225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p883 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p225) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h5200 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)

theorem step32589 (p6 p41 p45 p90 p127 p134 p186 : Prop)
    (h26831 : p45 ∨ p41)
    (h26586 : p90)
    (h26839 : p127 ∨ p6)
    (h17821 : (¬ p45) ∨ (¬ p90) ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p186)) : (¬ p186) ∨ (¬ p134) ∨ p41 ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p90 := by
    exact h26586
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17821 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)

theorem step32590 (p2 p17 p41 p45 p90 p192 p256 p303 p331 p574 p600 p1286 : Prop)
    (h26853 : p256 ∨ p17)
    (h26586 : p90)
    (h26831 : p45 ∨ p41)
    (h18544 : (¬ p2) ∨ (¬ p45) ∨ (¬ p90) ∨ (¬ p192) ∨ (¬ p256) ∨ (¬ p303) ∨ (¬ p331) ∨ (¬ p574) ∨ (¬ p600) ∨ (¬ p1286)) : p17 ∨ (¬ p192) ∨ (¬ p1286) ∨ p41 ∨ (¬ p574) ∨ (¬ p2) ∨ (¬ p331) ∨ (¬ p600) ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p17) := fun hu => hn (Or.inl hu)
  have u1 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p574 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p331 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p600 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p90 := by
    exact h26586
  have u11 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18544 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u11)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u2)

theorem step32591 (p41 p45 p90 p382 p406 p789 p797 p820 p858 : Prop)
    (h26869 : p406 ∨ p382)
    (h26586 : p90)
    (h26831 : p45 ∨ p41)
    (h26897 : p858 ∨ p789)
    (h17479 : (¬ p45) ∨ (¬ p90) ∨ (¬ p406) ∨ (¬ p797) ∨ (¬ p820) ∨ (¬ p858)) : (¬ p797) ∨ p382 ∨ p41 ∨ p789 ∨ (¬ p820) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p797 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p820 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p90 := by
    exact h26586
  have u7 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17479 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u8)

theorem step32592 (p2 p41 p45 p90 p185 p192 p237 p419 p665 p1115 p1116 : Prop)
    (h26831 : p45 ∨ p41)
    (h26586 : p90)
    (h26915 : p1116 ∨ p1115)
    (h26851 : p237 ∨ p185)
    (h20561 : (¬ p2) ∨ (¬ p45) ∨ (¬ p90) ∨ (¬ p192) ∨ (¬ p237) ∨ (¬ p419) ∨ (¬ p665) ∨ (¬ p1116)) : (¬ p2) ∨ (¬ p192) ∨ p41 ∨ p1115 ∨ (¬ p665) ∨ (¬ p419) ∨ p185 := by
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
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p90 := by
    exact h26586
  have u9 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20561 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u9)

theorem step32593 (p18 p19 p44 p90 p121 p189 p193 p228 p789 p858 p1385 : Prop)
    (h26829 : p19 ∨ p18)
    (h26845 : p193 ∨ p189)
    (h26586 : p90)
    (h26897 : p858 ∨ p789)
    (h19227 : (¬ p19) ∨ (¬ p44) ∨ (¬ p90) ∨ (¬ p121) ∨ (¬ p193) ∨ (¬ p228) ∨ (¬ p858) ∨ (¬ p1385)) : p18 ∨ p189 ∨ (¬ p228) ∨ (¬ p44) ∨ p789 ∨ (¬ p1385) ∨ (¬ p121) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p18) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p90 := by
    exact h26586
  have u10 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19227 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u5)

theorem step32597 (p156 p185 p382 p406 p789 p797 p820 p858 : Prop)
    (h26869 : p406 ∨ p382)
    (h26897 : p858 ∨ p789)
    (h20024 : (¬ p156) ∨ (¬ p185) ∨ (¬ p406) ∨ (¬ p797) ∨ (¬ p820) ∨ (¬ p858)) : (¬ p797) ∨ p382 ∨ (¬ p820) ∨ (¬ p185) ∨ (¬ p156) ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p797 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p820 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20024 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)

theorem step32598 (p303 p434 p790 p814 p1015 : Prop)
    (h26893 : p814 ∨ p790)
    (h19950 : (¬ p303) ∨ (¬ p434) ∨ (¬ p814) ∨ (¬ p1015)) : (¬ p1015) ∨ (¬ p434) ∨ p790 ∨ (¬ p303) := by
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
  have u2 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19950 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step32599 (p344 p728 p834 p1015 p1115 p1116 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h17378 : (¬ p344) ∨ (¬ p728) ∨ (¬ p834) ∨ (¬ p1015) ∨ (¬ p1116)) : (¬ p834) ∨ (¬ p1015) ∨ (¬ p344) ∨ p1115 ∨ (¬ p728) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p834 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17378 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)

theorem step32600 (p728 p790 p814 p1015 p1346 : Prop)
    (h26893 : p814 ∨ p790)
    (h17178 : (¬ p728) ∨ (¬ p814) ∨ (¬ p1015) ∨ (¬ p1346)) : (¬ p1015) ∨ (¬ p1346) ∨ (¬ p728) ∨ p790 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17178 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)

theorem step32628 (p125 p258 p262 p362 p434 p1545 : Prop)
    (h26865 : p362 ∨ p125)
    (h19199 : (¬ p258) ∨ (¬ p262) ∨ (¬ p362) ∨ (¬ p434) ∨ (¬ p1545)) : (¬ p434) ∨ (¬ p1545) ∨ (¬ p262) ∨ (¬ p258) ∨ p125 := by
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
  have u2 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19199 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)

theorem step32629 (p4 p8 p10 p137 p262 p310 p323 : Prop)
    (h26860 : (¬ p10) ∨ (¬ p323))
    (h13618 : (¬ p4) ∨ (¬ p8) ∨ (¬ p137) ∨ (¬ p262) ∨ (¬ p310) ∨ p323) : (¬ p10) ∨ (¬ p137) ∨ (¬ p310) ∨ (¬ p262) ∨ (¬ p8) ∨ (¬ p4) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p137 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p323) := by
    rcases h26860 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h13618 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)

theorem step32630 (p124 p262 p576 p581 p980 p983 p1076 p1077 : Prop)
    (h26903 : p983 ∨ p980)
    (h26911 : p1077 ∨ p1076)
    (h26879 : p581 ∨ p576)
    (h19857 : (¬ p124) ∨ (¬ p262) ∨ (¬ p581) ∨ (¬ p983) ∨ (¬ p1077)) : p980 ∨ p1076 ∨ (¬ p262) ∨ (¬ p124) ∨ p576 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19857 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)

#print axioms step32630

end NineRUPTrial
