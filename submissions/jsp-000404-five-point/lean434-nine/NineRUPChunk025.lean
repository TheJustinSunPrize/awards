import Mathlib.Tactic.Tauto

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

namespace NineRUPTrial

theorem step34037 (p3 p17 p125 p185 p225 p237 p303 p351 p362 p495 p544 p664 p790 p814 : Prop)
    (h26864 : (¬ p125) ∨ (¬ p362))
    (h26850 : (¬ p185) ∨ (¬ p237))
    (h26893 : p814 ∨ p790)
    (h26877 : p544 ∨ p225)
    (h25468 : p17 ∨ (¬ p495) ∨ (¬ p303) ∨ p362 ∨ (¬ p351) ∨ (¬ p664) ∨ (¬ p3) ∨ (¬ p814) ∨ (¬ p544) ∨ p237) : (¬ p125) ∨ p17 ∨ (¬ p185) ∨ p790 ∨ p225 ∨ (¬ p351) ∨ (¬ p664) ∨ (¬ p303) ∨ (¬ p3) ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p362) := by
    rcases h26864 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u11 : (¬ p237) := by
    rcases h26850 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u12 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u13 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h25468 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u7)
  · exact False.elim (u10 q3)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u12)
  · exact False.elim (q8 u13)
  · exact False.elim (u11 q9)

theorem step34038 (p15 p17 p71 p124 p194 p256 p258 p288 p304 p344 p382 p495 p1096 p1099 : Prop)
    (h26853 : p256 ∨ p17)
    (h26913 : p1099 ∨ p1096)
    (h26858 : (¬ p124) ∨ (¬ p304))
    (h26855 : p288 ∨ p258)
    (h24353 : (¬ p15) ∨ (¬ p382) ∨ (¬ p495) ∨ (¬ p194) ∨ (¬ p288) ∨ (¬ p71) ∨ (¬ p344) ∨ p304 ∨ (¬ p256) ∨ (¬ p1099)) : (¬ p71) ∨ (¬ p15) ∨ p17 ∨ (¬ p194) ∨ (¬ p344) ∨ (¬ p382) ∨ (¬ p495) ∨ p1096 ∨ (¬ p124) ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u12 : (¬ p304) := by
    rcases h26858 with q0 | q1
    · exact False.elim (q0 u8)
    · exact q1
  have u13 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h24353 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u13)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u4)
  · exact False.elim (u12 q7)
  · exact False.elim (q8 u10)
  · exact False.elim (q9 u11)

theorem step34040 (p86 p124 p125 p185 p237 p304 p348 p495 p533 p595 p616 p633 p636 p1287 p1325 : Prop)
    (h26859 : p304 ∨ p124)
    (h26885 : p636 ∨ p633)
    (h26883 : p616 ∨ p595)
    (h26851 : p237 ∨ p185)
    (h25456 : (¬ p237) ∨ (¬ p533) ∨ (¬ p1325) ∨ (¬ p616) ∨ (¬ p495) ∨ (¬ p86) ∨ (¬ p1287) ∨ (¬ p636) ∨ p125 ∨ (¬ p348) ∨ (¬ p304)) : p124 ∨ p633 ∨ (¬ p495) ∨ p595 ∨ (¬ p1325) ∨ (¬ p86) ∨ (¬ p533) ∨ (¬ p1287) ∨ (¬ p348) ∨ p185 ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p633) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u12 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u13 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u14 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h25456 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u14)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u13)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u12)
  · exact False.elim (u10 q8)
  · exact False.elim (q9 u8)
  · exact False.elim (q10 u11)

theorem step34041 (p124 p224 p227 p303 p304 p387 : Prop)
    (h26859 : p304 ∨ p124)
    (h26867 : p387 ∨ p303)
    (h25453 : (¬ p387) ∨ (¬ p224) ∨ (¬ p227) ∨ (¬ p304)) : p124 ∨ p303 ∨ (¬ p224) ∨ (¬ p227) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h25453 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step34042 (p124 p227 p304 p344 p346 : Prop)
    (h26859 : p304 ∨ p124)
    (h26863 : p346 ∨ p344)
    (h24674 : (¬ p346) ∨ (¬ p227) ∨ (¬ p304)) : p124 ∨ p344 ∨ (¬ p227) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h24674 with q0 | q1 | q2
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)

theorem step34043 (p124 p227 p303 p304 p387 p419 : Prop)
    (h26859 : p304 ∨ p124)
    (h26867 : p387 ∨ p303)
    (h24666 : (¬ p419) ∨ (¬ p304) ∨ (¬ p387) ∨ (¬ p227)) : p124 ∨ p303 ∨ (¬ p227) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h24666 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)

theorem step34044 (p227 p303 p324 p387 p419 p421 : Prop)
    (h26867 : p387 ∨ p303)
    (h26309 : (¬ p387) ∨ (¬ p227) ∨ (¬ p324) ∨ (¬ p421) ∨ (¬ p419)) : p303 ∨ (¬ p324) ∨ (¬ p421) ∨ (¬ p419) ∨ (¬ p227) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p324 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h26309 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)

theorem step34046 (p224 p344 p532 p595 p961 p980 p983 : Prop)
    (h26903 : p983 ∨ p980)
    (h25155 : (¬ p532) ∨ (¬ p983) ∨ (¬ p595) ∨ p224 ∨ (¬ p961) ∨ p344) : p980 ∨ (¬ p961) ∨ p344 ∨ (¬ p595) ∨ p224 ∨ (¬ p532) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h25155 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (u4 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (u2 q5)

theorem step34047 (p980 p983 p1287 p1325 : Prop)
    (h26903 : p983 ∨ p980)
    (h24861 : (¬ p983) ∨ (¬ p1287) ∨ (¬ p1325)) : p980 ∨ (¬ p1287) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : p1287 := by
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
  rcases h24861 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)

theorem step34061 (p101 p102 p121 p1035 p1452 : Prop)
    (h26837 : p102 ∨ p101)
    (h25013 : p1035 ∨ (¬ p102) ∨ (¬ p1452) ∨ (¬ p121)) : (¬ p1452) ∨ p101 ∨ p1035 ∨ (¬ p121) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p101) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1035) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h25013 with q0 | q1 | q2 | q3
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)

theorem step34062 (p161 p422 p1256 p1465 : Prop)
    (h26929 : p1256 ∨ p422)
    (h25332 : p1465 ∨ (¬ p1256) ∨ (¬ p161)) : p1465 ∨ p422 ∨ (¬ p161) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1465) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p422) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h25332 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)

theorem step34063 (p3 p224 p226 p1002 p1035 p1325 : Prop)
    (h26847 : p226 ∨ p3)
    (h25008 : (¬ p224) ∨ (¬ p1002) ∨ (¬ p1325) ∨ (¬ p1035) ∨ (¬ p226)) : (¬ p1002) ∨ (¬ p1035) ∨ (¬ p1325) ∨ (¬ p224) ∨ p3 := by
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
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h25008 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)

theorem step34066 (p160 p423 p1035 p1140 p1141 p1226 : Prop)
    (h26916 : (¬ p423) ∨ (¬ p1141))
    (h24399 : (¬ p1035) ∨ (¬ p1226) ∨ p160 ∨ p1141 ∨ p1140) : (¬ p1035) ∨ p160 ∨ p1140 ∨ (¬ p1226) ∨ (¬ p423) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p160) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p1141) := by
    rcases h26916 with q0 | q1
    · exact False.elim (q0 u4)
    · exact q1
  rcases h24399 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (u1 q2)
  · exact False.elim (u5 q3)
  · exact False.elim (u2 q4)

theorem step34069 (p124 p125 p304 p536 : Prop)
    (h26859 : p304 ∨ p124)
    (h25377 : p125 ∨ p536 ∨ (¬ p304)) : p536 ∨ p124 ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p536) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h25377 with q0 | q1 | q2
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)

theorem step34072 (p2 p125 p134 p142 p191 p207 p224 p303 p362 p387 p424 p657 p734 : Prop)
    (h26865 : p362 ∨ p125)
    (h26867 : p387 ∨ p303)
    (h26887 : p657 ∨ p224)
    (h26841 : p142 ∨ p134)
    (h25656 : (¬ p734) ∨ (¬ p362) ∨ (¬ p142) ∨ (¬ p387) ∨ p224 ∨ (¬ p657) ∨ (¬ p2) ∨ (¬ p191) ∨ (¬ p207) ∨ (¬ p424)) : (¬ p2) ∨ (¬ p734) ∨ p125 ∨ p303 ∨ (¬ p207) ∨ (¬ p191) ∨ (¬ p424) ∨ p224 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u12 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h25656 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u12)
  · exact False.elim (q3 u10)
  · exact False.elim (u7 q4)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u4)
  · exact False.elim (q9 u6)

theorem step34073 (p125 p134 p142 p207 p362 p420 p601 : Prop)
    (h26880 : (¬ p420) ∨ (¬ p601))
    (h26865 : p362 ∨ p125)
    (h26841 : p142 ∨ p134)
    (h25668 : p601 ∨ (¬ p362) ∨ (¬ p207) ∨ (¬ p142)) : (¬ p420) ∨ p125 ∨ p134 ∨ (¬ p207) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p125) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p601) := by
    rcases h26880 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u5 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h25668 with q0 | q1 | q2 | q3
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)

theorem step34074 (p121 p1206 p1213 : Prop)
    (h26922 : (¬ p121) ∨ (¬ p1206))
    (h24268 : p1213 ∨ p1206) : p1213 ∨ (¬ p121) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1213) := fun hu => hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1206) := by
    rcases h26922 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24268 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step34075 (p2 p12 p225 p540 p668 p1036 p1140 : Prop)
    (h26906 : (¬ p12) ∨ (¬ p1036))
    (h25337 : p1036 ∨ (¬ p668) ∨ (¬ p540) ∨ (¬ p225) ∨ (¬ p1140) ∨ (¬ p2)) : (¬ p2) ∨ (¬ p1140) ∨ (¬ p540) ∨ (¬ p12) ∨ (¬ p225) ∨ (¬ p668) := by
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
  have u2 : p540 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1036) := by
    rcases h26906 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h25337 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u0)

theorem step34077 (p15 p18 p19 p107 p121 p309 p419 p495 p499 p539 p600 p980 p983 p1055 p1103 p1286 p1449 : Prop)
    (h26875 : p499 ∨ p495)
    (h26902 : (¬ p980) ∨ (¬ p983))
    (h26829 : p19 ∨ p18)
    (h24856 : p983 ∨ (¬ p1055) ∨ (¬ p1286) ∨ (¬ p121) ∨ (¬ p419) ∨ (¬ p1103) ∨ (¬ p499) ∨ (¬ p15) ∨ (¬ p309) ∨ (¬ p107) ∨ (¬ p19) ∨ (¬ p539) ∨ (¬ p600) ∨ (¬ p1449)) : p495 ∨ (¬ p107) ∨ (¬ p309) ∨ (¬ p539) ∨ (¬ p1286) ∨ (¬ p980) ∨ (¬ p1449) ∨ (¬ p121) ∨ (¬ p1103) ∨ (¬ p15) ∨ (¬ p1055) ∨ (¬ p419) ∨ (¬ p600) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p495) := fun hu => hn (Or.inl hu)
  have u1 : p107 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p539 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1449 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p600 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))))
  have u14 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u15 : (¬ p983) := by
    rcases h26902 with q0 | q1
    · exact False.elim (q0 u5)
    · exact q1
  have u16 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u13 q1)
  rcases h24856 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13
  · exact False.elim (u15 q0)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u14)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u2)
  · exact False.elim (q9 u1)
  · exact False.elim (q10 u16)
  · exact False.elim (q11 u3)
  · exact False.elim (q12 u12)
  · exact False.elim (q13 u6)

theorem step34081 (p224 p234 p423 p657 p1141 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26887 : p657 ∨ p224)
    (h25522 : (¬ p1141) ∨ (¬ p234) ∨ (¬ p657)) : p423 ∨ p224 ∨ (¬ p234) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h25522 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)

theorem step34083 (p225 p542 p543 p544 : Prop)
    (h26876 : (¬ p225) ∨ (¬ p544))
    (h25287 : p542 ∨ p543 ∨ p544) : p542 ∨ p543 ∨ (¬ p225) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p542) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p543) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p544) := by
    rcases h26876 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h25287 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (u3 q2)

theorem step34084 (p633 p636 p640 : Prop)
    (h26884 : (¬ p633) ∨ (¬ p636))
    (h24301 : p640 ∨ p636) : p640 ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p640) := fun hu => hn (Or.inl hu)
  have u1 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p636) := by
    rcases h26884 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24301 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step34085 (p633 p636 p639 : Prop)
    (h26884 : (¬ p633) ∨ (¬ p636))
    (h24542 : p639 ∨ p636) : p639 ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p639) := fun hu => hn (Or.inl hu)
  have u1 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p636) := by
    rcases h26884 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24542 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step34087 (p419 p996 p998 p1002 p1012 : Prop)
    (h26904 : (¬ p419) ∨ (¬ p996))
    (h25756 : p998 ∨ (¬ p1012) ∨ p1002 ∨ p996) : p998 ∨ (¬ p1012) ∨ p1002 ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p998) := fun hu => hn (Or.inl hu)
  have u1 : p1012 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1002) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p996) := by
    rcases h26904 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h25756 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (u2 q2)
  · exact False.elim (u4 q3)

theorem step34088 (p63 p85 p163 p167 p224 p225 p918 p1385 p1393 : Prop)
    (h26835 : p85 ∨ p63)
    (h26933 : p1393 ∨ p1385)
    (h26842 : (¬ p163) ∨ (¬ p167))
    (h25301 : (¬ p918) ∨ (¬ p225) ∨ (¬ p1393) ∨ (¬ p85) ∨ (¬ p224) ∨ p167) : p63 ∨ p1385 ∨ (¬ p163) ∨ (¬ p918) ∨ (¬ p224) ∨ (¬ p225) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p63) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1385) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : (¬ p167) := by
    rcases h26842 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h25301 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u4)
  · exact False.elim (u8 q5)

theorem step34089 (p41 p163 p225 p344 p918 p928 : Prop)
    (h26900 : (¬ p918) ∨ (¬ p928))
    (h24583 : p928 ∨ (¬ p344) ∨ (¬ p41) ∨ p163 ∨ (¬ p225)) : (¬ p918) ∨ (¬ p41) ∨ (¬ p225) ∨ (¬ p344) ∨ p163 := by
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
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p928) := by
    rcases h26900 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h24583 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (u4 q3)
  · exact False.elim (q4 u2)

theorem step34091 (p382 p401 p406 : Prop)
    (h26868 : (¬ p382) ∨ (¬ p406))
    (h24501 : p401 ∨ p406) : p401 ∨ (¬ p382) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p401) := fun hu => hn (Or.inl hu)
  have u1 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p406) := by
    rcases h26868 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24501 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step34092 (p419 p479 p996 p1226 p1325 p1333 : Prop)
    (h26905 : p996 ∨ p419)
    (h26931 : p1333 ∨ p1325)
    (h24473 : (¬ p1226) ∨ (¬ p996) ∨ (¬ p1333) ∨ (¬ p479)) : (¬ p479) ∨ p419 ∨ (¬ p1226) ∨ p1325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p479 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p419) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h24473 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)

theorem step34101 (p15 p18 p69 p1096 : Prop)
    (h26833 : p69 ∨ p15)
    (h24262 : (¬ p1096) ∨ (¬ p18) ∨ (¬ p69)) : p15 ∨ (¬ p18) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p15) := fun hu => hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h24262 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)

theorem step34102 (p17 p63 p85 p495 p499 p1096 : Prop)
    (h26875 : p499 ∨ p495)
    (h26835 : p85 ∨ p63)
    (h24519 : (¬ p85) ∨ (¬ p1096) ∨ (¬ p499) ∨ (¬ p17)) : (¬ p1096) ∨ p495 ∨ (¬ p17) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h24519 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)

theorem step34103 (p17 p39 p63 p85 p225 p303 p434 p595 p690 p1055 p1061 p1076 p1077 p1096 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26834 : (¬ p63) ∨ (¬ p85))
    (h26908 : (¬ p1055) ∨ (¬ p1061))
    (h25478 : (¬ p303) ∨ (¬ p17) ∨ p225 ∨ (¬ p1096) ∨ (¬ p595) ∨ (¬ p690) ∨ (¬ p434) ∨ (¬ p1077) ∨ (¬ p39) ∨ p1061 ∨ p85) : p225 ∨ p1076 ∨ (¬ p63) ∨ (¬ p595) ∨ (¬ p434) ∨ (¬ p1055) ∨ (¬ p690) ∨ (¬ p1096) ∨ (¬ p17) ∨ (¬ p39) ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p225) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u12 : (¬ p85) := by
    rcases h26834 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u13 : (¬ p1061) := by
    rcases h26908 with q0 | q1
    · exact False.elim (q0 u5)
    · exact q1
  rcases h25478 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u8)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u11)
  · exact False.elim (q8 u9)
  · exact False.elim (u13 q9)
  · exact False.elim (u12 q10)

theorem step34106 (p41 p189 p193 p918 p928 p1055 p1076 p1077 : Prop)
    (h26900 : (¬ p918) ∨ (¬ p928))
    (h26911 : p1077 ∨ p1076)
    (h26845 : p193 ∨ p189)
    (h25612 : (¬ p41) ∨ p928 ∨ (¬ p1077) ∨ (¬ p193) ∨ (¬ p1055)) : (¬ p918) ∨ (¬ p41) ∨ p1076 ∨ p189 ∨ (¬ p1055) := by
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
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p928) := by
    rcases h26900 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u6 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h25612 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u4)

theorem step34107 (p6 p41 p105 p127 p187 p918 p928 : Prop)
    (h26839 : p127 ∨ p6)
    (h26900 : (¬ p918) ∨ (¬ p928))
    (h25252 : p928 ∨ (¬ p127) ∨ (¬ p105) ∨ (¬ p41) ∨ (¬ p187)) : p6 ∨ (¬ p918) ∨ (¬ p187) ∨ (¬ p41) ∨ (¬ p105) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p6) := fun hu => hn (Or.inl hu)
  have u1 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : (¬ p928) := by
    rcases h26900 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h25252 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)

theorem step34111 (p3 p6 p10 p18 p125 p134 p142 p163 p191 p224 p226 p303 p323 p344 p362 p382 p406 p521 p557 p657 p680 p789 p839 p1076 p1077 p1140 p1159 p1212 : Prop)
    (h26869 : p406 ∨ p382)
    (h26861 : p323 ∨ p10)
    (h26865 : p362 ∨ p125)
    (h26841 : p142 ∨ p134)
    (h26911 : p1077 ∨ p1076)
    (h26886 : (¬ p224) ∨ (¬ p657))
    (h26847 : p226 ∨ p3)
    (h26919 : p1159 ∨ p1140)
    (h25735 : p18 ∨ (¬ p163) ∨ (¬ p142) ∨ (¬ p362) ∨ (¬ p839) ∨ (¬ p521) ∨ (¬ p789) ∨ (¬ p191) ∨ (¬ p557) ∨ (¬ p680) ∨ (¬ p1077) ∨ (¬ p226) ∨ (¬ p344) ∨ p657 ∨ (¬ p1212) ∨ (¬ p1159) ∨ (¬ p303) ∨ (¬ p323) ∨ (¬ p406) ∨ (¬ p6)) : p18 ∨ p382 ∨ (¬ p303) ∨ p10 ∨ (¬ p163) ∨ (¬ p521) ∨ (¬ p789) ∨ p125 ∨ (¬ p839) ∨ (¬ p191) ∨ p134 ∨ p1076 ∨ (¬ p344) ∨ (¬ p224) ∨ p3 ∨ (¬ p557) ∨ (¬ p680) ∨ (¬ p1212) ∨ p1140 ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p18) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p521 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p839 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))
  have u15 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))
  have u16 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))
  have u17 : p1212 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))))
  have u18 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))))
  have u19 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))))))))))
  have u20 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u21 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u22 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u23 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u10 q1)
  have u24 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  have u25 : (¬ p657) := by
    rcases h26886 with q0 | q1
    · exact False.elim (q0 u13)
    · exact q1
  have u26 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u14 q1)
  have u27 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u18 q1)
  rcases h25735 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14 | q15 | q16 | q17 | q18 | q19
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u23)
  · exact False.elim (q3 u22)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u15)
  · exact False.elim (q9 u16)
  · exact False.elim (q10 u24)
  · exact False.elim (q11 u26)
  · exact False.elim (q12 u12)
  · exact False.elim (u25 q13)
  · exact False.elim (q14 u17)
  · exact False.elim (q15 u27)
  · exact False.elim (q16 u2)
  · exact False.elim (q17 u21)
  · exact False.elim (q18 u20)
  · exact False.elim (q19 u19)

theorem step34114 (p2 p12 p15 p69 p419 p1036 p1076 p1077 : Prop)
    (h26907 : p1036 ∨ p12)
    (h26833 : p69 ∨ p15)
    (h26911 : p1077 ∨ p1076)
    (h25626 : (¬ p69) ∨ (¬ p2) ∨ (¬ p419) ∨ (¬ p1036) ∨ (¬ p1077)) : (¬ p2) ∨ p12 ∨ p15 ∨ (¬ p419) ∨ p1076 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h25626 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)

theorem step34117 (p12 p224 p225 p382 p544 p657 p1036 : Prop)
    (h26877 : p544 ∨ p225)
    (h26886 : (¬ p224) ∨ (¬ p657))
    (h26907 : p1036 ∨ p12)
    (h25581 : p382 ∨ (¬ p1036) ∨ p657 ∨ (¬ p544)) : p382 ∨ p225 ∨ (¬ p224) ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : (¬ p657) := by
    rcases h26886 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u6 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h25581 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u4)

theorem step34119 (p12 p163 p167 p185 p1036 p1346 : Prop)
    (h26907 : p1036 ∨ p12)
    (h26842 : (¬ p163) ∨ (¬ p167))
    (h24978 : (¬ p185) ∨ (¬ p1346) ∨ (¬ p1036) ∨ p12 ∨ p167) : (¬ p1346) ∨ p12 ∨ (¬ p163) ∨ (¬ p185) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : (¬ p167) := by
    rcases h26842 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h24978 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (u1 q3)
  · exact False.elim (u5 q4)

theorem step34120 (p12 p225 p544 p664 p980 p1465 : Prop)
    (h26877 : p544 ∨ p225)
    (h24760 : (¬ p1465) ∨ p980 ∨ p12 ∨ (¬ p664) ∨ (¬ p544)) : p980 ∨ p225 ∨ (¬ p664) ∨ (¬ p1465) ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h24760 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (u0 q1)
  · exact False.elim (u4 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step34123 (p8 p163 p224 p424 p657 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h26887 : p657 ∨ p224)
    (h24685 : (¬ p163) ∨ (¬ p657) ∨ (¬ p8) ∨ (¬ p796)) : p424 ∨ (¬ p163) ∨ (¬ p8) ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h24685 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step34124 (p12 p134 p142 p207 p310 p1036 p1055 p1061 p1074 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h26906 : (¬ p12) ∨ (¬ p1036))
    (h26841 : p142 ∨ p134)
    (h25658 : (¬ p1074) ∨ (¬ p1061) ∨ p1036 ∨ (¬ p310) ∨ (¬ p207) ∨ (¬ p142)) : (¬ p1074) ∨ p1055 ∨ (¬ p12) ∨ (¬ p310) ∨ p134 ∨ (¬ p207) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : (¬ p1036) := by
    rcases h26906 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u8 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h25658 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u8)

theorem step34130 (p1076 p1077 p1078 : Prop)
    (h26910 : (¬ p1076) ∨ (¬ p1077))
    (h25509 : p1078 ∨ p1077) : p1078 ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1078) := fun hu => hn (Or.inl hu)
  have u1 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1077) := by
    rcases h26910 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h25509 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step34134 (p6 p101 p102 p121 p161 p1074 p1081 p1096 p1099 p1229 p1232 p1330 p1366 : Prop)
    (h26837 : p102 ∨ p101)
    (h26927 : p1232 ∨ p1229)
    (h26913 : p1099 ∨ p1096)
    (h26312 : (¬ p1366) ∨ (¬ p1232) ∨ p6 ∨ (¬ p161) ∨ (¬ p1074) ∨ (¬ p121) ∨ (¬ p1330) ∨ (¬ p1081) ∨ (¬ p1099) ∨ (¬ p102)) : (¬ p1366) ∨ (¬ p161) ∨ p6 ∨ p101 ∨ (¬ p1081) ∨ p1229 ∨ (¬ p1330) ∨ (¬ p1074) ∨ (¬ p121) ∨ p1096 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u12 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h26312 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u11)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u12)
  · exact False.elim (q9 u10)

theorem step34144 (p6 p15 p69 p101 p102 p127 p134 p142 p191 p224 p227 p303 p344 p382 p406 p423 p496 p521 p545 p789 p839 p1002 p1141 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26869 : p406 ∨ p382)
    (h26833 : p69 ∨ p15)
    (h26841 : p142 ∨ p134)
    (h26837 : p102 ∨ p101)
    (h26838 : (¬ p6) ∨ (¬ p127))
    (h25736 : (¬ p102) ∨ (¬ p496) ∨ (¬ p69) ∨ (¬ p1141) ∨ (¬ p142) ∨ (¬ p227) ∨ (¬ p839) ∨ (¬ p521) ∨ (¬ p789) ∨ (¬ p191) ∨ (¬ p545) ∨ (¬ p344) ∨ (¬ p224) ∨ (¬ p303) ∨ (¬ p1002) ∨ (¬ p406) ∨ p127) : p423 ∨ p382 ∨ (¬ p496) ∨ p15 ∨ p134 ∨ (¬ p303) ∨ (¬ p227) ∨ (¬ p521) ∨ (¬ p789) ∨ p101 ∨ (¬ p839) ∨ (¬ p191) ∨ (¬ p224) ∨ (¬ p344) ∨ (¬ p6) ∨ (¬ p545) ∨ (¬ p1002) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p227 := by
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
  have u9 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p839 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))
  have u15 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))
  have u16 : p1002 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))))))))
  have u17 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u18 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u19 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u20 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u21 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  have u22 : (¬ p127) := by
    rcases h26838 with q0 | q1
    · exact False.elim (q0 u14)
    · exact q1
  rcases h25736 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14 | q15 | q16
  · exact False.elim (q0 u21)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u19)
  · exact False.elim (q3 u17)
  · exact False.elim (q4 u20)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u8)
  · exact False.elim (q9 u11)
  · exact False.elim (q10 u15)
  · exact False.elim (q11 u13)
  · exact False.elim (q12 u12)
  · exact False.elim (q13 u5)
  · exact False.elim (q14 u16)
  · exact False.elim (q15 u18)
  · exact False.elim (u22 q16)

theorem step34146 (p101 p102 p124 p134 p142 p191 : Prop)
    (h26837 : p102 ∨ p101)
    (h26841 : p142 ∨ p134)
    (h25739 : p124 ∨ (¬ p102) ∨ (¬ p142) ∨ (¬ p191)) : p124 ∨ p101 ∨ (¬ p191) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p101) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h25739 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)

theorem step34148 (p17 p194 p256 p258 p288 p344 p382 p419 p545 : Prop)
    (h26853 : p256 ∨ p17)
    (h26855 : p288 ∨ p258)
    (h24328 : p419 ∨ (¬ p545) ∨ (¬ p382) ∨ (¬ p194) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p256)) : (¬ p194) ∨ (¬ p382) ∨ p17 ∨ p258 ∨ p419 ∨ (¬ p545) ∨ (¬ p344) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h24328 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step34149 (p10 p323 p324 : Prop)
    (h26860 : (¬ p10) ∨ (¬ p323))
    (h24642 : p324 ∨ p323) : p324 ∨ (¬ p10) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p324) := fun hu => hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p323) := by
    rcases h26860 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24642 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step34155 (p12 p13 p17 p101 p124 p126 p161 p189 p256 p304 p422 p424 p595 p600 p616 p836 p840 p1084 : Prop)
    (h26859 : p304 ∨ p124)
    (h26883 : p616 ∨ p595)
    (h26853 : p256 ∨ p17)
    (h26895 : p840 ∨ p836)
    (h26307 : p161 ∨ (¬ p256) ∨ (¬ p126) ∨ (¬ p12) ∨ (¬ p1084) ∨ (¬ p101) ∨ (¬ p616) ∨ (¬ p304) ∨ (¬ p189) ∨ (¬ p13) ∨ (¬ p840) ∨ (¬ p424) ∨ (¬ p600) ∨ p422) : (¬ p101) ∨ p124 ∨ p595 ∨ (¬ p424) ∨ p161 ∨ (¬ p1084) ∨ p17 ∨ (¬ p126) ∨ (¬ p189) ∨ (¬ p13) ∨ p836 ∨ (¬ p12) ∨ (¬ p600) ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p161) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p600 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))))
  have u14 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u15 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u16 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u17 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u10 q1)
  rcases h26307 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u16)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u15)
  · exact False.elim (q7 u14)
  · exact False.elim (q8 u8)
  · exact False.elim (q9 u9)
  · exact False.elim (q10 u17)
  · exact False.elim (q11 u3)
  · exact False.elim (q12 u12)
  · exact False.elim (u13 q13)

theorem step34156 (p41 p45 p161 p1225 p1489 : Prop)
    (h26925 : p1225 ∨ p161)
    (h26831 : p45 ∨ p41)
    (h24817 : (¬ p1489) ∨ (¬ p1225) ∨ (¬ p45)) : p161 ∨ (¬ p1489) ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p161) := fun hu => hn (Or.inl hu)
  have u1 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h24817 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)

theorem step34157 (p161 p420 p532 p1225 p1307 : Prop)
    (h26925 : p1225 ∨ p161)
    (h24922 : (¬ p1225) ∨ (¬ p532) ∨ (¬ p1307) ∨ (¬ p420)) : p161 ∨ (¬ p420) ∨ (¬ p532) ∨ (¬ p1307) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p161) := fun hu => hn (Or.inl hu)
  have u1 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1307 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h24922 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)

theorem step34158 (p161 p303 p603 p1225 p1325 : Prop)
    (h26925 : p1225 ∨ p161)
    (h24843 : (¬ p1225) ∨ (¬ p1325) ∨ (¬ p303) ∨ (¬ p603)) : p161 ∨ (¬ p603) ∨ (¬ p1325) ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p161) := fun hu => hn (Or.inl hu)
  have u1 : p603 := by
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
  have u4 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h24843 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)

theorem step34159 (p160 p161 p1225 p1235 : Prop)
    (h26925 : p1225 ∨ p161)
    (h25014 : p160 ∨ (¬ p1235) ∨ (¬ p1225)) : p160 ∨ p161 ∨ (¬ p1235) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p160) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p161) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1235 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h25014 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)

theorem step34163 (p3 p101 p107 p134 p142 p226 p344 p382 p406 p419 p789 p858 : Prop)
    (h26896 : (¬ p789) ∨ (¬ p858))
    (h26869 : p406 ∨ p382)
    (h26846 : (¬ p3) ∨ (¬ p226))
    (h26841 : p142 ∨ p134)
    (h25179 : p101 ∨ (¬ p107) ∨ (¬ p142) ∨ (¬ p419) ∨ p858 ∨ (¬ p406) ∨ (¬ p344) ∨ p226) : (¬ p789) ∨ p382 ∨ (¬ p3) ∨ (¬ p344) ∨ p101 ∨ (¬ p107) ∨ (¬ p419) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p107 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p858) := by
    rcases h26896 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u9 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : (¬ p226) := by
    rcases h26846 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u11 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h25179 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u6)
  · exact False.elim (u8 q4)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u3)
  · exact False.elim (u10 q7)

theorem step34164 (p6 p10 p191 p224 p351 p382 p406 p424 : Prop)
    (h26869 : p406 ∨ p382)
    (h25732 : (¬ p10) ∨ (¬ p424) ∨ (¬ p351) ∨ (¬ p406) ∨ (¬ p224) ∨ (¬ p191) ∨ (¬ p6)) : p382 ∨ (¬ p10) ∨ (¬ p351) ∨ (¬ p6) ∨ (¬ p191) ∨ (¬ p424) ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p351 := by
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
  have u5 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h25732 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u3)

theorem step34165 (p224 p419 p422 p424 p542 p657 p996 p1256 : Prop)
    (h26928 : (¬ p422) ∨ (¬ p1256))
    (h26887 : p657 ∨ p224)
    (h26904 : (¬ p419) ∨ (¬ p996))
    (h25646 : p1256 ∨ (¬ p542) ∨ p996 ∨ (¬ p657) ∨ (¬ p424)) : (¬ p422) ∨ p224 ∨ (¬ p419) ∨ (¬ p424) ∨ (¬ p542) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p1256) := by
    rcases h26928 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u6 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : (¬ p996) := by
    rcases h26904 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h25646 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)

theorem step34168 (p6 p41 p45 p134 p142 p576 p581 : Prop)
    (h26879 : p581 ∨ p576)
    (h26831 : p45 ∨ p41)
    (h26841 : p142 ∨ p134)
    (h25312 : (¬ p6) ∨ (¬ p581) ∨ (¬ p142) ∨ (¬ p45)) : p576 ∨ p41 ∨ p134 ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p576) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p41) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
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
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h25312 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)

theorem step34174 (p3 p6 p87 p163 p188 p226 p576 p581 : Prop)
    (h26847 : p226 ∨ p3)
    (h26879 : p581 ∨ p576)
    (h24927 : (¬ p163) ∨ (¬ p188) ∨ (¬ p226) ∨ (¬ p6) ∨ (¬ p87) ∨ (¬ p581)) : p3 ∨ p576 ∨ (¬ p87) ∨ (¬ p188) ∨ (¬ p6) ∨ (¬ p163) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h24927 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)

theorem step34175 (p6 p18 p19 p41 p45 p87 p189 p193 : Prop)
    (h26830 : (¬ p41) ∨ (¬ p45))
    (h26829 : p19 ∨ p18)
    (h26844 : (¬ p189) ∨ (¬ p193))
    (h25714 : p45 ∨ (¬ p19) ∨ (¬ p87) ∨ (¬ p6) ∨ p193) : (¬ p41) ∨ p18 ∨ (¬ p189) ∨ (¬ p87) ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p18) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p45) := by
    rcases h26830 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : (¬ p193) := by
    rcases h26844 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h25714 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (u7 q4)

theorem step34176 (p2 p6 p87 p234 p329 p576 p581 p790 : Prop)
    (h26879 : p581 ∨ p576)
    (h24930 : (¬ p2) ∨ (¬ p329) ∨ (¬ p234) ∨ p790 ∨ (¬ p6) ∨ (¬ p87) ∨ (¬ p581)) : (¬ p2) ∨ (¬ p234) ∨ p790 ∨ (¬ p329) ∨ p576 ∨ (¬ p87) ∨ (¬ p6) := by
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
  have u2 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p329 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h24930 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (u2 q3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u7)

theorem step34180 (p10 p126 p134 p323 p576 p1385 p1393 : Prop)
    (h26860 : (¬ p10) ∨ (¬ p323))
    (h26933 : p1393 ∨ p1385)
    (h25596 : p323 ∨ p134 ∨ (¬ p1393) ∨ (¬ p126) ∨ (¬ p576)) : (¬ p10) ∨ (¬ p126) ∨ p1385 ∨ p134 ∨ (¬ p576) := by
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
  have u2 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p323) := by
    rcases h26860 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u6 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h25596 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u5 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)

theorem step34181 (p125 p126 p301 p576 p1385 p1393 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h26856 : (¬ p126) ∨ (¬ p301))
    (h25594 : (¬ p125) ∨ (¬ p1393) ∨ p301 ∨ (¬ p576)) : (¬ p576) ∨ p1385 ∨ (¬ p125) ∨ (¬ p126) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1385) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : (¬ p301) := by
    rcases h26856 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h25594 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u0)

theorem step34183 (p10 p101 p102 p124 p134 p304 p323 p344 p346 p576 p1385 p1393 : Prop)
    (h26862 : (¬ p344) ∨ (¬ p346))
    (h26837 : p102 ∨ p101)
    (h26858 : (¬ p124) ∨ (¬ p304))
    (h26933 : p1393 ∨ p1385)
    (h26861 : p323 ∨ p10)
    (h25601 : p346 ∨ p304 ∨ (¬ p102) ∨ p134 ∨ (¬ p323) ∨ (¬ p1393) ∨ (¬ p576)) : (¬ p344) ∨ p101 ∨ (¬ p124) ∨ p1385 ∨ p10 ∨ p134 ∨ (¬ p576) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p101) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p346) := by
    rcases h26862 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u8 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : (¬ p304) := by
    rcases h26858 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u10 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h25601 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u7 q0)
  · exact False.elim (u9 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u6)

theorem step34185 (p15 p189 p193 p234 p576 : Prop)
    (h26845 : p193 ∨ p189)
    (h24260 : (¬ p576) ∨ (¬ p193) ∨ (¬ p234) ∨ p15) : (¬ p576) ∨ p189 ∨ (¬ p234) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h24260 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)

theorem step34186 (p234 p424 p576 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h24251 : (¬ p796) ∨ (¬ p576) ∨ (¬ p234)) : p424 ∨ (¬ p576) ∨ (¬ p234) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h24251 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)

theorem step34187 (p3 p6 p12 p105 p127 p1055 p1061 : Prop)
    (h26839 : p127 ∨ p6)
    (h26908 : (¬ p1055) ∨ (¬ p1061))
    (h24396 : p1061 ∨ (¬ p12) ∨ (¬ p127) ∨ (¬ p105) ∨ p3) : p6 ∨ (¬ p1055) ∨ (¬ p12) ∨ p3 ∨ (¬ p105) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p6) := fun hu => hn (Or.inl hu)
  have u1 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : (¬ p1061) := by
    rcases h26908 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24396 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (u3 q4)

theorem step34188 (p6 p8 p63 p101 p102 p121 p163 p167 p189 p193 p224 p389 p657 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26836 : (¬ p101) ∨ (¬ p102))
    (h26887 : p657 ∨ p224)
    (h26843 : p167 ∨ p163)
    (h26844 : (¬ p189) ∨ (¬ p193))
    (h25715 : (¬ p1206) ∨ (¬ p8) ∨ (¬ p389) ∨ (¬ p657) ∨ p63 ∨ (¬ p6) ∨ (¬ p167) ∨ p193 ∨ p102) : p121 ∨ (¬ p389) ∨ (¬ p101) ∨ p63 ∨ p224 ∨ (¬ p6) ∨ p163 ∨ (¬ p189) ∨ (¬ p8) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : (¬ p102) := by
    rcases h26836 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u11 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u12 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u13 : (¬ p193) := by
    rcases h26844 with q0 | q1
    · exact False.elim (q0 u7)
    · exact q1
  rcases h25715 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u11)
  · exact False.elim (u3 q4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u12)
  · exact False.elim (u13 q7)
  · exact False.elim (u10 q8)

theorem step34191 (p11 p17 p189 p193 p256 p961 p1443 : Prop)
    (h26852 : (¬ p17) ∨ (¬ p256))
    (h26935 : p1443 ∨ p11)
    (h26845 : p193 ∨ p189)
    (h25233 : (¬ p193) ∨ (¬ p1443) ∨ (¬ p961) ∨ p256) : (¬ p961) ∨ (¬ p17) ∨ p11 ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p256) := by
    rcases h26852 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  have u5 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h25233 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (u4 q3)

theorem step34193 (p2 p6 p63 p85 p127 p303 p424 p576 p581 : Prop)
    (h26839 : p127 ∨ p6)
    (h26835 : p85 ∨ p63)
    (h26878 : (¬ p576) ∨ (¬ p581))
    (h25328 : p581 ∨ (¬ p85) ∨ (¬ p303) ∨ (¬ p424) ∨ (¬ p127) ∨ (¬ p2)) : (¬ p2) ∨ p6 ∨ (¬ p424) ∨ p63 ∨ (¬ p576) ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : (¬ p581) := by
    rcases h26878 with q0 | q1
    · exact False.elim (q0 u4)
    · exact q1
  rcases h25328 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u0)

theorem step34195 (p125 p126 p301 p576 p581 : Prop)
    (h26857 : p301 ∨ p126)
    (h26878 : (¬ p576) ∨ (¬ p581))
    (h24885 : p581 ∨ p125 ∨ (¬ p301)) : p126 ∨ (¬ p576) ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : (¬ p581) := by
    rcases h26878 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24885 with q0 | q1 | q2
  · exact False.elim (u4 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)

theorem step34196 (p41 p63 p189 p193 p224 p344 p576 p581 p657 : Prop)
    (h26878 : (¬ p576) ∨ (¬ p581))
    (h26844 : (¬ p189) ∨ (¬ p193))
    (h26887 : p657 ∨ p224)
    (h25248 : p581 ∨ (¬ p344) ∨ (¬ p657) ∨ (¬ p41) ∨ p63 ∨ p193) : (¬ p576) ∨ (¬ p41) ∨ (¬ p344) ∨ (¬ p189) ∨ p224 ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p581) := by
    rcases h26878 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u7 : (¬ p193) := by
    rcases h26844 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  have u8 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h25248 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u1)
  · exact False.elim (u5 q4)
  · exact False.elim (u7 q5)

theorem step34197 (p1385 p1388 p1393 : Prop)
    (h26932 : (¬ p1385) ∨ (¬ p1393))
    (h24849 : p1388 ∨ p1393) : p1388 ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1388) := fun hu => hn (Or.inl hu)
  have u1 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1393) := by
    rcases h26932 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24849 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step34199 (p4 p8 p17 p194 p224 p256 p258 p288 p434 p710 p1044 p1076 p1077 p1140 : Prop)
    (h26853 : p256 ∨ p17)
    (h26889 : p710 ∨ p8)
    (h26911 : p1077 ∨ p1076)
    (h26855 : p288 ∨ p258)
    (h25681 : (¬ p288) ∨ (¬ p256) ∨ (¬ p434) ∨ (¬ p710) ∨ p1140 ∨ (¬ p4) ∨ (¬ p194) ∨ (¬ p1044) ∨ p224 ∨ (¬ p1077)) : (¬ p434) ∨ p1140 ∨ (¬ p4) ∨ p224 ∨ (¬ p1044) ∨ p17 ∨ (¬ p194) ∨ p8 ∨ p1076 ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1140) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1044 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u11 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u12 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u13 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h25681 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u13)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u11)
  · exact False.elim (u1 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u4)
  · exact False.elim (u3 q8)
  · exact False.elim (q9 u12)

theorem step34200 (p15 p39 p69 p790 p1385 : Prop)
    (h26833 : p69 ∨ p15)
    (h24705 : (¬ p790) ∨ (¬ p39) ∨ (¬ p1385) ∨ (¬ p69)) : (¬ p790) ∨ (¬ p1385) ∨ (¬ p39) ∨ p15 := by
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
  have u2 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h24705 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)

theorem step34202 (p455 p456 p461 : Prop)
    (h26870 : (¬ p455) ∨ (¬ p456))
    (h24566 : p461 ∨ p456) : p461 ∨ (¬ p455) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p461) := fun hu => hn (Or.inl hu)
  have u1 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p456) := by
    rcases h26870 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24566 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step34205 (p6 p21 p72 p101 p124 p125 p127 p234 p304 p329 p350 p382 p420 p601 p1187 p1366 : Prop)
    (h26859 : p304 ∨ p124)
    (h26881 : p601 ∨ p420)
    (h26921 : p1187 ∨ p234)
    (h26839 : p127 ∨ p6)
    (h25207 : (¬ p1366) ∨ (¬ p1187) ∨ (¬ p382) ∨ (¬ p304) ∨ (¬ p350) ∨ (¬ p101) ∨ (¬ p601) ∨ p125 ∨ (¬ p72) ∨ (¬ p127) ∨ (¬ p21) ∨ (¬ p329)) : (¬ p1366) ∨ p124 ∨ (¬ p382) ∨ (¬ p72) ∨ p420 ∨ (¬ p21) ∨ (¬ p101) ∨ p125 ∨ (¬ p329) ∨ p234 ∨ (¬ p350) ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p21 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p329 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p234) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))
  have u12 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u13 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u14 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  have u15 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  rcases h25207 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u14)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u12)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u13)
  · exact False.elim (u7 q7)
  · exact False.elim (q8 u3)
  · exact False.elim (q9 u15)
  · exact False.elim (q10 u5)
  · exact False.elim (q11 u8)

theorem step34210 (p88 p125 p362 p576 p581 p1385 : Prop)
    (h26879 : p581 ∨ p576)
    (h26865 : p362 ∨ p125)
    (h24841 : (¬ p581) ∨ (¬ p362) ∨ (¬ p88) ∨ (¬ p1385)) : (¬ p1385) ∨ p576 ∨ p125 ∨ (¬ p88) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h24841 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)

theorem step34211 (p163 p166 p167 p172 : Prop)
    (h26842 : (¬ p163) ∨ (¬ p167))
    (h25038 : p172 ∨ p167 ∨ p166) : p172 ∨ p166 ∨ (¬ p163) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p172) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p166) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p167) := by
    rcases h26842 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h25038 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (u1 q2)

theorem step34212 (p6 p127 p186 p189 p193 p326 p790 p1346 : Prop)
    (h26839 : p127 ∨ p6)
    (h26845 : p193 ∨ p189)
    (h25210 : (¬ p193) ∨ p1346 ∨ p790 ∨ (¬ p186) ∨ (¬ p326) ∨ (¬ p127)) : p6 ∨ p1346 ∨ p790 ∨ p189 ∨ (¬ p186) ∨ (¬ p326) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p6) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1346) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p326 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h25210 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u7)
  · exact False.elim (u1 q1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)

theorem step34214 (p434 p495 p499 p595 p690 : Prop)
    (h26875 : p499 ∨ p495)
    (h24578 : p595 ∨ (¬ p434) ∨ (¬ p499) ∨ (¬ p690)) : (¬ p434) ∨ (¬ p690) ∨ p495 ∨ p595 := by
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
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h24578 with q0 | q1 | q2 | q3
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)

theorem step34223 (p897 p899 p904 : Prop)
    (h26898 : (¬ p897) ∨ (¬ p904))
    (h25274 : p899 ∨ p904) : p899 ∨ (¬ p897) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p899) := fun hu => hn (Or.inl hu)
  have u1 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p904) := by
    rcases h26898 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h25274 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step34226 (p8 p15 p69 p224 p710 p1229 p1542 : Prop)
    (h26833 : p69 ∨ p15)
    (h26889 : p710 ∨ p8)
    (h25411 : (¬ p69) ∨ (¬ p224) ∨ (¬ p1542) ∨ (¬ p1229) ∨ (¬ p710)) : (¬ p1542) ∨ p15 ∨ (¬ p1229) ∨ (¬ p224) ∨ p8 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h25411 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)

theorem step34230 (p3 p14 p64 p86 p189 p193 p226 p234 p790 : Prop)
    (h26847 : p226 ∨ p3)
    (h26845 : p193 ∨ p189)
    (h24924 : (¬ p193) ∨ (¬ p226) ∨ p790 ∨ (¬ p86) ∨ (¬ p64) ∨ (¬ p234) ∨ (¬ p14)) : p3 ∨ p189 ∨ (¬ p234) ∨ (¬ p64) ∨ (¬ p14) ∨ p790 ∨ (¬ p86) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h24924 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u7)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u4)

theorem step34237 (p15 p69 p224 p303 p344 p348 p351 p386 p387 p495 p595 p616 p657 p1084 : Prop)
    (h26867 : p387 ∨ p303)
    (h26882 : (¬ p595) ∨ (¬ p616))
    (h26887 : p657 ∨ p224)
    (h26833 : p69 ∨ p15)
    (h24702 : (¬ p495) ∨ (¬ p1084) ∨ (¬ p351) ∨ (¬ p348) ∨ (¬ p344) ∨ (¬ p386) ∨ (¬ p387) ∨ p616 ∨ (¬ p657) ∨ (¬ p69)) : (¬ p386) ∨ p303 ∨ (¬ p595) ∨ (¬ p344) ∨ (¬ p351) ∨ (¬ p348) ∨ (¬ p495) ∨ p224 ∨ (¬ p1084) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p386 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u11 : (¬ p616) := by
    rcases h26882 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u12 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u13 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h24702 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u10)
  · exact False.elim (u11 q7)
  · exact False.elim (q8 u12)
  · exact False.elim (q9 u13)

theorem step34238 (p1 p2 p3 p125 p134 p191 p207 p225 p226 p362 p544 p1076 p1077 : Prop)
    (h26847 : p226 ∨ p3)
    (h26877 : p544 ∨ p225)
    (h26910 : (¬ p1076) ∨ (¬ p1077))
    (h26865 : p362 ∨ p125)
    (h25665 : p1077 ∨ (¬ p544) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p226) ∨ (¬ p362) ∨ (¬ p207) ∨ p134 ∨ (¬ p191)) : p3 ∨ (¬ p1) ∨ (¬ p2) ∨ p225 ∨ (¬ p1076) ∨ (¬ p191) ∨ p134 ∨ (¬ p207) ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p1 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : (¬ p1077) := by
    rcases h26910 with q0 | q1
    · exact False.elim (q0 u4)
    · exact q1
  have u12 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h25665 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u11 q0)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u12)
  · exact False.elim (q6 u7)
  · exact False.elim (u6 q7)
  · exact False.elim (q8 u5)

theorem step34240 (p6 p101 p127 p134 p142 p163 p186 p1076 p1077 : Prop)
    (h26839 : p127 ∨ p6)
    (h26911 : p1077 ∨ p1076)
    (h26840 : (¬ p134) ∨ (¬ p142))
    (h24309 : (¬ p163) ∨ (¬ p186) ∨ (¬ p127) ∨ p101 ∨ p142 ∨ (¬ p1077)) : p6 ∨ (¬ p186) ∨ p1076 ∨ p101 ∨ (¬ p134) ∨ (¬ p163) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p6) := fun hu => hn (Or.inl hu)
  have u1 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : (¬ p142) := by
    rcases h26840 with q0 | q1
    · exact False.elim (q0 u4)
    · exact q1
  rcases h24309 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (u3 q3)
  · exact False.elim (u8 q4)
  · exact False.elim (q5 u7)

theorem step34243 (p124 p258 p261 p288 p304 p520 p575 p633 p636 p790 : Prop)
    (h26859 : p304 ∨ p124)
    (h26855 : p288 ∨ p258)
    (h26885 : p636 ∨ p633)
    (h25560 : (¬ p288) ∨ (¬ p636) ∨ (¬ p304) ∨ (¬ p520) ∨ (¬ p790) ∨ (¬ p575) ∨ (¬ p261)) : p124 ∨ p258 ∨ (¬ p575) ∨ p633 ∨ (¬ p520) ∨ (¬ p790) ∨ (¬ p261) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p258) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p575 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p633) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p520 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h25560 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u6)

theorem step34250 (p2 p63 p185 p237 p303 p344 p346 p349 p387 p419 p582 p1274 : Prop)
    (h26867 : p387 ∨ p303)
    (h26851 : p237 ∨ p185)
    (h26862 : (¬ p344) ∨ (¬ p346))
    (h25497 : p346 ∨ (¬ p582) ∨ (¬ p237) ∨ (¬ p349) ∨ (¬ p419) ∨ (¬ p2) ∨ p63 ∨ (¬ p387) ∨ (¬ p1274)) : (¬ p2) ∨ p303 ∨ p185 ∨ (¬ p582) ∨ (¬ p419) ∨ (¬ p1274) ∨ (¬ p344) ∨ (¬ p349) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1274 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : (¬ p346) := by
    rcases h26862 with q0 | q1
    · exact False.elim (q0 u6)
    · exact q1
  rcases h25497 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u11 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u0)
  · exact False.elim (u8 q6)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u5)

theorem step34253 (p2 p17 p41 p45 p101 p102 p121 p134 p210 p224 p258 p262 p286 p288 p344 p346 p481 p576 p581 p816 p897 p918 p928 p1035 p1038 p1080 p1096 p1099 p1206 p1335 p1385 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26855 : p288 ∨ p258)
    (h26863 : p346 ∨ p344)
    (h26873 : p481 ∨ p2)
    (h26831 : p45 ∨ p41)
    (h26837 : p102 ∨ p101)
    (h26901 : p928 ∨ p918)
    (h26913 : p1099 ∨ p1096)
    (h26879 : p581 ∨ p576)
    (h25308 : (¬ p897) ∨ (¬ p210) ∨ (¬ p481) ∨ (¬ p1335) ∨ (¬ p346) ∨ (¬ p224) ∨ (¬ p1035) ∨ (¬ p1038) ∨ (¬ p1080) ∨ (¬ p102) ∨ (¬ p288) ∨ (¬ p286) ∨ (¬ p1099) ∨ (¬ p581) ∨ (¬ p1206) ∨ (¬ p928) ∨ (¬ p262) ∨ (¬ p17) ∨ (¬ p816) ∨ p134 ∨ (¬ p45) ∨ p1385) : p121 ∨ (¬ p897) ∨ p134 ∨ p258 ∨ p344 ∨ p2 ∨ (¬ p210) ∨ p1385 ∨ (¬ p224) ∨ p41 ∨ (¬ p1080) ∨ (¬ p1335) ∨ (¬ p1035) ∨ p101 ∨ (¬ p1038) ∨ (¬ p816) ∨ p918 ∨ p1096 ∨ (¬ p17) ∨ (¬ p262) ∨ p576 ∨ (¬ p286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p1080 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : p1038 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))
  have u15 : p816 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))
  have u16 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))
  have u17 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))))
  have u18 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))))
  have u19 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))))))
  have u20 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))))))
  have u21 : p286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))))))))))))
  have u22 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u23 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u24 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u25 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u26 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  have u27 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u13 q1)
  have u28 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u16 q1)
  have u29 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u17 q1)
  have u30 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u20 q1)
  rcases h25308 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14 | q15 | q16 | q17 | q18 | q19 | q20 | q21
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u25)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u24)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u12)
  · exact False.elim (q7 u14)
  · exact False.elim (q8 u10)
  · exact False.elim (q9 u27)
  · exact False.elim (q10 u23)
  · exact False.elim (q11 u21)
  · exact False.elim (q12 u29)
  · exact False.elim (q13 u30)
  · exact False.elim (q14 u22)
  · exact False.elim (q15 u28)
  · exact False.elim (q16 u19)
  · exact False.elim (q17 u18)
  · exact False.elim (q18 u15)
  · exact False.elim (u2 q19)
  · exact False.elim (q20 u26)
  · exact False.elim (u7 q21)

theorem step34258 (p126 p301 p303 p381 p382 p532 p576 p789 p1287 p1508 : Prop)
    (h26856 : (¬ p126) ∨ (¬ p301))
    (h25223 : (¬ p789) ∨ (¬ p381) ∨ (¬ p1287) ∨ (¬ p303) ∨ (¬ p382) ∨ (¬ p1508) ∨ p301 ∨ (¬ p532) ∨ (¬ p576)) : (¬ p789) ∨ (¬ p1508) ∨ (¬ p126) ∨ (¬ p303) ∨ (¬ p381) ∨ (¬ p576) ∨ (¬ p382) ∨ (¬ p532) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p381 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p301) := by
    rcases h26856 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h25223 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (u9 q6)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u5)

theorem step34262 (p2 p477 p481 : Prop)
    (h26872 : (¬ p2) ∨ (¬ p481))
    (h24346 : p477 ∨ p481) : p477 ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p477) := fun hu => hn (Or.inl hu)
  have u1 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p481) := by
    rcases h26872 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24346 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step34268 (p125 p362 p363 : Prop)
    (h26864 : (¬ p125) ∨ (¬ p362))
    (h24742 : p363 ∨ p362) : p363 ∨ (¬ p125) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p363) := fun hu => hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p362) := by
    rcases h26864 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24742 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step34274 (p2 p41 p45 p224 p481 p728 p816 p897 p898 p1096 p1099 p1385 : Prop)
    (h26831 : p45 ∨ p41)
    (h26873 : p481 ∨ p2)
    (h26913 : p1099 ∨ p1096)
    (h25302 : (¬ p728) ∨ (¬ p898) ∨ (¬ p897) ∨ (¬ p481) ∨ (¬ p816) ∨ (¬ p1099) ∨ (¬ p45) ∨ p1385 ∨ (¬ p224)) : (¬ p728) ∨ p1385 ∨ p41 ∨ (¬ p816) ∨ (¬ p224) ∨ p2 ∨ (¬ p897) ∨ (¬ p898) ∨ p1096 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1385) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p816 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p898 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u11 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h25302 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u9)
  · exact False.elim (u1 q7)
  · exact False.elim (q8 u4)

theorem step34276 (p3 p11 p17 p108 p226 p256 p940 p985 p1443 p1452 : Prop)
    (h26847 : p226 ∨ p3)
    (h26935 : p1443 ∨ p11)
    (h26853 : p256 ∨ p17)
    (h24967 : (¬ p226) ∨ (¬ p985) ∨ (¬ p940) ∨ (¬ p108) ∨ (¬ p1452) ∨ (¬ p1443) ∨ (¬ p256)) : (¬ p940) ∨ p3 ∨ p11 ∨ (¬ p1452) ∨ (¬ p108) ∨ (¬ p985) ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h24967 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u9)

theorem step34277 (p2 p163 p185 p189 p192 p193 p303 p387 p419 p517 : Prop)
    (h26845 : p193 ∨ p189)
    (h26867 : p387 ∨ p303)
    (h25483 : (¬ p185) ∨ (¬ p517) ∨ (¬ p193) ∨ p163 ∨ (¬ p192) ∨ (¬ p419) ∨ (¬ p2) ∨ (¬ p387)) : (¬ p517) ∨ (¬ p185) ∨ p189 ∨ p163 ∨ (¬ p192) ∨ p303 ∨ (¬ p2) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p517 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h25483 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u8)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u9)

theorem step34284 (p6 p101 p102 p127 p195 p258 : Prop)
    (h26837 : p102 ∨ p101)
    (h26839 : p127 ∨ p6)
    (h25121 : (¬ p102) ∨ (¬ p127) ∨ (¬ p258) ∨ (¬ p195)) : p101 ∨ p6 ∨ (¬ p258) ∨ (¬ p195) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p101) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h25121 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)

theorem step34285 (p3 p195 p225 p544 p836 p840 : Prop)
    (h26894 : (¬ p836) ∨ (¬ p840))
    (h26877 : p544 ∨ p225)
    (h25541 : p840 ∨ (¬ p195) ∨ (¬ p3) ∨ (¬ p544)) : (¬ p836) ∨ p225 ∨ (¬ p3) ∨ (¬ p195) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p840) := by
    rcases h26894 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u5 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h25541 with q0 | q1 | q2 | q3
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)

theorem step34288 (p3 p18 p19 p63 p165 p195 p225 p544 p918 p928 p1465 : Prop)
    (h26829 : p19 ∨ p18)
    (h26901 : p928 ∨ p918)
    (h26877 : p544 ∨ p225)
    (h25548 : (¬ p1465) ∨ (¬ p19) ∨ (¬ p165) ∨ (¬ p928) ∨ (¬ p195) ∨ (¬ p3) ∨ (¬ p544) ∨ (¬ p63)) : (¬ p165) ∨ p18 ∨ (¬ p1465) ∨ (¬ p63) ∨ p918 ∨ (¬ p3) ∨ (¬ p195) ∨ p225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p165 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p18) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h25548 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u3)

theorem step34292 (p6 p12 p18 p19 p24 p41 p45 p64 p83 p134 p142 p171 p188 p224 p539 p836 p918 p927 p928 p1096 p1099 p1385 : Prop)
    (h26831 : p45 ∨ p41)
    (h26841 : p142 ∨ p134)
    (h26913 : p1099 ∨ p1096)
    (h26901 : p928 ∨ p918)
    (h26829 : p19 ∨ p18)
    (h25304 : (¬ p6) ∨ (¬ p24) ∨ (¬ p19) ∨ (¬ p64) ∨ (¬ p1099) ∨ (¬ p188) ∨ (¬ p45) ∨ (¬ p171) ∨ (¬ p836) ∨ (¬ p927) ∨ (¬ p928) ∨ (¬ p539) ∨ p12 ∨ p1385 ∨ (¬ p83) ∨ (¬ p224) ∨ (¬ p142)) : (¬ p171) ∨ (¬ p836) ∨ (¬ p24) ∨ p12 ∨ (¬ p539) ∨ (¬ p188) ∨ p41 ∨ p134 ∨ (¬ p83) ∨ p1096 ∨ (¬ p64) ∨ (¬ p6) ∨ (¬ p224) ∨ p918 ∨ p1385 ∨ (¬ p927) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p171 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p539 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))
  have u15 : p927 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))
  have u16 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))))))))
  have u17 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u18 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u19 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  have u20 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u13 q1)
  have u21 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u16 q1)
  rcases h25304 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14 | q15 | q16
  · exact False.elim (q0 u11)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u21)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u19)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u17)
  · exact False.elim (q7 u0)
  · exact False.elim (q8 u1)
  · exact False.elim (q9 u15)
  · exact False.elim (q10 u20)
  · exact False.elim (q11 u4)
  · exact False.elim (u3 q12)
  · exact False.elim (u14 q13)
  · exact False.elim (q14 u8)
  · exact False.elim (q15 u12)
  · exact False.elim (q16 u18)

theorem step34294 (p422 p1252 p1256 : Prop)
    (h26928 : (¬ p422) ∨ (¬ p1256))
    (h24949 : p1252 ∨ p1256) : p1252 ∨ (¬ p422) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1252) := fun hu => hn (Or.inl hu)
  have u1 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1256) := by
    rcases h26928 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24949 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step34302 (p8 p15 p63 p710 p897 p904 p927 p1097 : Prop)
    (h26899 : p904 ∨ p897)
    (h26889 : p710 ∨ p8)
    (h25382 : (¬ p15) ∨ (¬ p927) ∨ (¬ p904) ∨ (¬ p1097) ∨ (¬ p710) ∨ p63) : p897 ∨ p8 ∨ (¬ p927) ∨ p63 ∨ (¬ p1097) ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p897) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p8) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p927 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1097 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p15 := by
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
  rcases h25382 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u7)
  · exact False.elim (u3 q5)

theorem step34308 (p225 p542 p544 p555 : Prop)
    (h26876 : (¬ p225) ∨ (¬ p544))
    (h25281 : p555 ∨ p542 ∨ p544) : p555 ∨ p542 ∨ (¬ p225) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p555) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p542) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p544) := by
    rcases h26876 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h25281 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (u3 q2)

theorem step34315 (p125 p362 p364 : Prop)
    (h26864 : (¬ p125) ∨ (¬ p362))
    (h26505 : p364 ∨ p362) : p364 ∨ (¬ p125) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p364) := fun hu => hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p362) := by
    rcases h26864 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h26505 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step34332 (p3 p17 p63 p124 p125 p185 p225 p303 p304 p495 p789 p790 p814 p858 p1325 : Prop)
    (h26893 : p814 ∨ p790)
    (h26859 : p304 ∨ p124)
    (h26897 : p858 ∨ p789)
    (h25467 : (¬ p17) ∨ p63 ∨ (¬ p495) ∨ (¬ p303) ∨ (¬ p125) ∨ p1325 ∨ (¬ p304) ∨ (¬ p858) ∨ (¬ p3) ∨ (¬ p814) ∨ p225 ∨ (¬ p185)) : (¬ p125) ∨ (¬ p3) ∨ p1325 ∨ (¬ p17) ∨ p63 ∨ p790 ∨ p225 ∨ (¬ p185) ∨ (¬ p495) ∨ p124 ∨ p789 ∨ (¬ p303) := by
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
  have u2 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))
  have u12 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u13 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  have u14 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u10 q1)
  rcases h25467 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (q0 u3)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u0)
  · exact False.elim (u2 q5)
  · exact False.elim (q6 u13)
  · exact False.elim (q7 u14)
  · exact False.elim (q8 u1)
  · exact False.elim (q9 u12)
  · exact False.elim (u6 q10)
  · exact False.elim (q11 u7)

theorem step34333 (p2 p63 p134 p424 p495 p499 : Prop)
    (h26875 : p499 ∨ p495)
    (h25330 : p63 ∨ (¬ p499) ∨ p134 ∨ (¬ p424) ∨ (¬ p2)) : (¬ p2) ∨ p495 ∨ p63 ∨ (¬ p424) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h25330 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (u4 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u0)

theorem step34334 (p8 p17 p41 p63 p101 p102 p189 p193 p224 p256 p344 p657 : Prop)
    (h26837 : p102 ∨ p101)
    (h26852 : (¬ p17) ∨ (¬ p256))
    (h26844 : (¬ p189) ∨ (¬ p193))
    (h26887 : p657 ∨ p224)
    (h25249 : (¬ p102) ∨ (¬ p8) ∨ p256 ∨ (¬ p344) ∨ (¬ p657) ∨ (¬ p41) ∨ p63 ∨ p193) : (¬ p344) ∨ p63 ∨ p101 ∨ (¬ p17) ∨ (¬ p8) ∨ (¬ p41) ∨ (¬ p189) ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p63) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : (¬ p256) := by
    rcases h26852 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  have u10 : (¬ p193) := by
    rcases h26844 with q0 | q1
    · exact False.elim (q0 u6)
    · exact q1
  have u11 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h25249 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u4)
  · exact False.elim (u9 q2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u5)
  · exact False.elim (u1 q6)
  · exact False.elim (u10 q7)

theorem step34337 (p41 p63 p124 p189 p224 p344 p657 : Prop)
    (h26887 : p657 ∨ p224)
    (h25247 : (¬ p124) ∨ (¬ p344) ∨ (¬ p657) ∨ (¬ p41) ∨ p63 ∨ (¬ p189)) : (¬ p41) ∨ (¬ p344) ∨ (¬ p124) ∨ (¬ p189) ∨ p63 ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
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
  have u4 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h25247 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u0)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u3)

theorem step34338 (p41 p45 p101 p102 p134 p142 p188 p189 p224 p595 p616 p665 p790 p1076 p1077 p1392 : Prop)
    (h26831 : p45 ∨ p41)
    (h26911 : p1077 ∨ p1076)
    (h26883 : p616 ∨ p595)
    (h26841 : p142 ∨ p134)
    (h26837 : p102 ∨ p101)
    (h25600 : (¬ p790) ∨ (¬ p1077) ∨ (¬ p616) ∨ (¬ p188) ∨ (¬ p189) ∨ (¬ p665) ∨ (¬ p224) ∨ (¬ p102) ∨ (¬ p45) ∨ (¬ p142) ∨ (¬ p1392)) : (¬ p790) ∨ (¬ p1392) ∨ p41 ∨ (¬ p224) ∨ p1076 ∨ p595 ∨ (¬ p665) ∨ (¬ p189) ∨ (¬ p188) ∨ p134 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1392 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u12 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u13 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u14 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  have u15 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u10 q1)
  rcases h25600 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u12)
  · exact False.elim (q2 u13)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u15)
  · exact False.elim (q8 u11)
  · exact False.elim (q9 u14)
  · exact False.elim (q10 u1)

theorem step34339 (p3 p39 p63 p225 p226 p668 p918 p928 p1115 p1116 p1392 : Prop)
    (h26847 : p226 ∨ p3)
    (h26901 : p928 ∨ p918)
    (h26915 : p1116 ∨ p1115)
    (h25682 : (¬ p63) ∨ (¬ p39) ∨ (¬ p928) ∨ (¬ p1392) ∨ (¬ p1116) ∨ (¬ p226) ∨ (¬ p225) ∨ (¬ p668)) : p3 ∨ (¬ p225) ∨ (¬ p39) ∨ (¬ p1392) ∨ p918 ∨ (¬ p668) ∨ p1115 ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1392 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h25682 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u5)

theorem step34347 (p63 p224 p789 p836 p858 p918 p928 : Prop)
    (h26896 : (¬ p789) ∨ (¬ p858))
    (h26901 : p928 ∨ p918)
    (h25558 : p858 ∨ (¬ p928) ∨ (¬ p224) ∨ p836 ∨ (¬ p63)) : (¬ p789) ∨ (¬ p224) ∨ p836 ∨ p918 ∨ (¬ p63) := by
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
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p858) := by
    rcases h26896 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u6 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h25558 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u1)
  · exact False.elim (u2 q3)
  · exact False.elim (q4 u4)

theorem step34348 (p8 p87 p710 p836 p918 p928 : Prop)
    (h26901 : p928 ∨ p918)
    (h26889 : p710 ∨ p8)
    (h25383 : p836 ∨ (¬ p928) ∨ (¬ p710) ∨ (¬ p87)) : p918 ∨ p8 ∨ (¬ p87) ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p918) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p8) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h25383 with q0 | q1 | q2 | q3
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)

theorem step34349 (p16 p17 p126 p301 p303 p438 p595 p1286 : Prop)
    (h26857 : p301 ∨ p126)
    (h25637 : (¬ p438) ∨ (¬ p595) ∨ (¬ p1286) ∨ p303 ∨ (¬ p17) ∨ (¬ p16) ∨ (¬ p301)) : (¬ p1286) ∨ p126 ∨ (¬ p595) ∨ p303 ∨ (¬ p17) ∨ (¬ p438) ∨ (¬ p16) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h25637 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step34350 (p224 p344 p419 p657 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h26886 : (¬ p224) ∨ (¬ p657))
    (h24520 : p657 ∨ p344 ∨ (¬ p996)) : p419 ∨ (¬ p224) ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : (¬ p657) := by
    rcases h26886 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24520 with q0 | q1 | q2
  · exact False.elim (u4 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)

theorem step34352 (p10 p101 p306 p323 p350 p420 p536 p601 p1538 : Prop)
    (h26881 : p601 ∨ p420)
    (h26861 : p323 ∨ p10)
    (h25212 : (¬ p1538) ∨ (¬ p601) ∨ (¬ p536) ∨ (¬ p101) ∨ (¬ p350) ∨ (¬ p306) ∨ (¬ p323)) : (¬ p350) ∨ (¬ p1538) ∨ p420 ∨ (¬ p536) ∨ p10 ∨ (¬ p101) ∨ (¬ p306) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1538 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p536 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h25212 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u8)

theorem step34354 (p2 p3 p226 p344 : Prop)
    (h26846 : (¬ p3) ∨ (¬ p226))
    (h25174 : (¬ p2) ∨ (¬ p344) ∨ p226) : (¬ p2) ∨ (¬ p3) ∨ (¬ p344) := by
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
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p226) := by
    rcases h26846 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h25174 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (u3 q2)

theorem step34355 (p1 p2 p6 p382 p419 p477 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h24511 : p6 ∨ (¬ p1) ∨ (¬ p477) ∨ (¬ p2) ∨ (¬ p996) ∨ (¬ p382)) : p419 ∨ (¬ p382) ∨ (¬ p2) ∨ p6 ∨ (¬ p1) ∨ (¬ p477) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p477 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h24511 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)

theorem step34359 (p2 p63 p192 p303 p349 p387 p419 : Prop)
    (h26867 : p387 ∨ p303)
    (h25480 : p192 ∨ p63 ∨ (¬ p2) ∨ (¬ p419) ∨ (¬ p349) ∨ (¬ p387)) : (¬ p2) ∨ p303 ∨ p192 ∨ (¬ p419) ∨ (¬ p349) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p192) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h25480 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u2 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)

theorem step34360 (p2 p41 p45 p63 p85 p303 p349 p387 p419 : Prop)
    (h26835 : p85 ∨ p63)
    (h26831 : p45 ∨ p41)
    (h26867 : p387 ∨ p303)
    (h25479 : (¬ p45) ∨ (¬ p85) ∨ (¬ p2) ∨ (¬ p419) ∨ (¬ p349) ∨ (¬ p387)) : (¬ p2) ∨ (¬ p349) ∨ p63 ∨ p41 ∨ (¬ p419) ∨ p303 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h25479 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u8)

theorem step34363 (p15 p68 p69 p72 : Prop)
    (h26832 : (¬ p15) ∨ (¬ p69))
    (h25060 : p72 ∨ p69 ∨ p68) : p72 ∨ p68 ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p72) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p68) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p69) := by
    rcases h26832 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h25060 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (u1 q2)

theorem step34364 (p14 p18 p41 p45 p90 p186 p189 p193 p229 p918 p928 : Prop)
    (h26831 : p45 ∨ p41)
    (h26845 : p193 ∨ p189)
    (h26848 : (¬ p14) ∨ (¬ p229))
    (h26586 : p90)
    (h26901 : p928 ∨ p918)
    (h24842 : (¬ p18) ∨ p229 ∨ (¬ p928) ∨ (¬ p45) ∨ (¬ p90) ∨ (¬ p193) ∨ (¬ p186)) : p41 ∨ p189 ∨ (¬ p186) ∨ (¬ p14) ∨ p918 ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p41) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : (¬ p229) := by
    rcases h26848 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  have u9 : p90 := by
    exact h26586
  have u10 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h24842 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u2)

theorem step34365 (p15 p18 p69 p1213 p1229 : Prop)
    (h26833 : p69 ∨ p15)
    (h24312 : (¬ p69) ∨ (¬ p18) ∨ (¬ p1213) ∨ (¬ p1229)) : p15 ∨ (¬ p18) ∨ (¬ p1213) ∨ (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p15) := fun hu => hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1213 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h24312 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)

theorem step34367 (p15 p69 p71 : Prop)
    (h26832 : (¬ p15) ∨ (¬ p69))
    (h24318 : p71 ∨ p69) : p71 ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p71) := fun hu => hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p69) := by
    rcases h26832 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24318 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step34372 (p17 p125 p141 p163 p167 p185 p189 p256 p286 : Prop)
    (h26852 : (¬ p17) ∨ (¬ p256))
    (h26842 : (¬ p163) ∨ (¬ p167))
    (h24977 : p185 ∨ p256 ∨ (¬ p189) ∨ (¬ p141) ∨ (¬ p125) ∨ (¬ p286) ∨ p167) : p185 ∨ (¬ p125) ∨ (¬ p17) ∨ (¬ p286) ∨ (¬ p189) ∨ (¬ p163) ∨ (¬ p141) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p185) := fun hu => hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p256) := by
    rcases h26852 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u8 : (¬ p167) := by
    rcases h26842 with q0 | q1
    · exact False.elim (q0 u5)
    · exact q1
  rcases h24977 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u3)
  · exact False.elim (u8 q6)

theorem step34374 (p12 p15 p17 p18 p69 p88 p104 p124 p256 p258 p421 p595 p633 p665 p1192 p1226 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26853 : p256 ∨ p17)
    (h26833 : p69 ∨ p15)
    (h24377 : (¬ p595) ∨ (¬ p12) ∨ (¬ p1192) ∨ (¬ p69) ∨ (¬ p421) ∨ (¬ p633) ∨ p18 ∨ (¬ p104) ∨ p88 ∨ (¬ p665) ∨ (¬ p1226) ∨ (¬ p1333) ∨ (¬ p258) ∨ (¬ p124) ∨ (¬ p256)) : p88 ∨ (¬ p104) ∨ p1325 ∨ p17 ∨ (¬ p258) ∨ (¬ p12) ∨ (¬ p595) ∨ (¬ p1226) ∨ p15 ∨ (¬ p633) ∨ (¬ p1192) ∨ p18 ∨ (¬ p124) ∨ (¬ p421) ∨ (¬ p665) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p88) := fun hu => hn (Or.inl hu)
  have u1 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p1192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))))))
  have u15 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u16 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u17 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h24377 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u17)
  · exact False.elim (q4 u13)
  · exact False.elim (q5 u9)
  · exact False.elim (u11 q6)
  · exact False.elim (q7 u1)
  · exact False.elim (u0 q8)
  · exact False.elim (q9 u14)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u15)
  · exact False.elim (q12 u4)
  · exact False.elim (q13 u12)
  · exact False.elim (q14 u16)

theorem step34380 (p101 p102 p105 : Prop)
    (h26836 : (¬ p101) ∨ (¬ p102))
    (h24233 : p102 ∨ p105) : (¬ p101) ∨ p105 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p105) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p102) := by
    rcases h26836 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h24233 with q0 | q1
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)

theorem step34386 (p41 p47 p63 p101 p102 p163 p234 p344 p480 p563 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26836 : (¬ p101) ∨ (¬ p102))
    (h25533 : (¬ p163) ∨ (¬ p563) ∨ (¬ p344) ∨ (¬ p41) ∨ (¬ p47) ∨ (¬ p63) ∨ p102 ∨ (¬ p1187) ∨ (¬ p480)) : (¬ p47) ∨ (¬ p344) ∨ (¬ p563) ∨ p234 ∨ (¬ p480) ∨ (¬ p101) ∨ (¬ p163) ∨ (¬ p41) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p563 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p234) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p480 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : (¬ p102) := by
    rcases h26836 with q0 | q1
    · exact False.elim (q0 u5)
    · exact q1
  rcases h25533 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u8)
  · exact False.elim (u10 q6)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u4)

theorem step34387 (p6 p101 p102 p124 p134 p142 p163 p167 : Prop)
    (h26836 : (¬ p101) ∨ (¬ p102))
    (h26843 : p167 ∨ p163)
    (h26841 : p142 ∨ p134)
    (h24648 : (¬ p124) ∨ (¬ p167) ∨ p102 ∨ p6 ∨ (¬ p142)) : (¬ p101) ∨ p6 ∨ (¬ p124) ∨ p163 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p102) := by
    rcases h26836 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u6 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h24648 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (u5 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u7)

theorem step34389 (p3 p10 p12 p14 p15 p24 p69 p126 p157 p163 p169 p225 p229 p323 p382 p495 p499 p519 p536 p544 p600 p633 p665 p789 p980 p1095 p1250 p1311 : Prop)
    (h26833 : p69 ∨ p15)
    (h26875 : p499 ∨ p495)
    (h26848 : (¬ p14) ∨ (¬ p229))
    (h26877 : p544 ∨ p225)
    (h26861 : p323 ∨ p10)
    (h25672 : (¬ p499) ∨ (¬ p980) ∨ p789 ∨ (¬ p69) ∨ (¬ p1250) ∨ (¬ p169) ∨ (¬ p163) ∨ (¬ p3) ∨ (¬ p382) ∨ (¬ p665) ∨ p633 ∨ (¬ p544) ∨ p229 ∨ (¬ p1311) ∨ (¬ p1095) ∨ (¬ p157) ∨ (¬ p536) ∨ (¬ p12) ∨ (¬ p24) ∨ (¬ p600) ∨ (¬ p519) ∨ (¬ p126) ∨ (¬ p323)) : (¬ p536) ∨ p633 ∨ (¬ p980) ∨ (¬ p519) ∨ p789 ∨ (¬ p24) ∨ (¬ p163) ∨ (¬ p169) ∨ p15 ∨ (¬ p3) ∨ (¬ p382) ∨ (¬ p665) ∨ p495 ∨ (¬ p1250) ∨ (¬ p1095) ∨ (¬ p14) ∨ (¬ p157) ∨ (¬ p12) ∨ (¬ p1311) ∨ p225 ∨ (¬ p600) ∨ (¬ p126) ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p536 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p633) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p519 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p169 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : p1250 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))
  have u15 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))
  have u16 : p157 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))
  have u17 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))))
  have u18 : p1311 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))))
  have u19 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))))))
  have u20 : p600 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))))))
  have u21 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))))))))
  have u22 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))))))))))))))
  have u23 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u24 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u12 q1)
  have u25 : (¬ p229) := by
    rcases h26848 with q0 | q1
    · exact False.elim (q0 u15)
    · exact q1
  have u26 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u19 q1)
  have u27 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u22 q1)
  rcases h25672 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14 | q15 | q16 | q17 | q18 | q19 | q20 | q21 | q22
  · exact False.elim (q0 u24)
  · exact False.elim (q1 u2)
  · exact False.elim (u4 q2)
  · exact False.elim (q3 u23)
  · exact False.elim (q4 u13)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u10)
  · exact False.elim (q9 u11)
  · exact False.elim (u1 q10)
  · exact False.elim (q11 u26)
  · exact False.elim (u25 q12)
  · exact False.elim (q13 u18)
  · exact False.elim (q14 u14)
  · exact False.elim (q15 u16)
  · exact False.elim (q16 u0)
  · exact False.elim (q17 u17)
  · exact False.elim (q18 u5)
  · exact False.elim (q19 u20)
  · exact False.elim (q20 u3)
  · exact False.elim (q21 u21)
  · exact False.elim (q22 u27)

theorem step34390 (p8 p17 p310 p344 p710 p1096 p1229 : Prop)
    (h26888 : (¬ p8) ∨ (¬ p710))
    (h24324 : p344 ∨ p710 ∨ (¬ p310) ∨ p17 ∨ p1096 ∨ (¬ p1229)) : (¬ p1229) ∨ (¬ p8) ∨ (¬ p310) ∨ p1096 ∨ p17 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p710) := by
    rcases h26888 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24324 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (u4 q3)
  · exact False.elim (u3 q4)
  · exact False.elim (q5 u0)

theorem step34391 (p8 p710 p734 p1055 : Prop)
    (h26889 : p710 ∨ p8)
    (h25378 : (¬ p734) ∨ p1055 ∨ (¬ p710)) : p1055 ∨ p8 ∨ (¬ p734) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1055) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p8) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h25378 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)

theorem step34394 (p126 p268 p301 p303 p382 p406 : Prop)
    (h26857 : p301 ∨ p126)
    (h26869 : p406 ∨ p382)
    (h24652 : (¬ p303) ∨ (¬ p406) ∨ (¬ p301) ∨ (¬ p268)) : p126 ∨ p382 ∨ (¬ p268) ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p268 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h24652 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)

theorem step34399 (p6 p127 p207 : Prop)
    (h26838 : (¬ p6) ∨ (¬ p127))
    (h24943 : p207 ∨ p127) : p207 ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p207) := fun hu => hn (Or.inl hu)
  have u1 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p127) := by
    rcases h26838 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24943 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step34400 (p3 p14 p63 p85 p229 : Prop)
    (h26849 : p229 ∨ p14)
    (h26835 : p85 ∨ p63)
    (h24936 : (¬ p229) ∨ (¬ p3) ∨ (¬ p85)) : p14 ∨ (¬ p3) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h24936 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)

theorem step34402 (p3 p6 p11 p17 p47 p63 p85 p86 p127 p256 p423 p1096 p1099 p1140 p1443 p1452 p1562 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26835 : p85 ∨ p63)
    (h26935 : p1443 ∨ p11)
    (h26838 : (¬ p6) ∨ (¬ p127))
    (h26853 : p256 ∨ p17)
    (h24962 : (¬ p3) ∨ p1140 ∨ (¬ p85) ∨ p127 ∨ (¬ p47) ∨ p423 ∨ (¬ p1562) ∨ (¬ p1452) ∨ (¬ p1099) ∨ (¬ p1443) ∨ (¬ p256) ∨ (¬ p86)) : (¬ p1562) ∨ p423 ∨ (¬ p86) ∨ p1096 ∨ (¬ p3) ∨ p63 ∨ (¬ p47) ∨ p11 ∨ (¬ p6) ∨ p17 ∨ p1140 ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1562 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p423) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))
  have u12 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u13 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u14 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u15 : (¬ p127) := by
    rcases h26838 with q0 | q1
    · exact False.elim (q0 u8)
    · exact q1
  have u16 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h24962 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (q0 u4)
  · exact False.elim (u10 q1)
  · exact False.elim (q2 u13)
  · exact False.elim (u15 q3)
  · exact False.elim (q4 u6)
  · exact False.elim (u1 q5)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u11)
  · exact False.elim (q8 u12)
  · exact False.elim (q9 u14)
  · exact False.elim (q10 u16)
  · exact False.elim (q11 u2)

theorem step34409 (p63 p85 p121 p227 p495 p582 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26835 : p85 ∨ p63)
    (h24690 : p495 ∨ (¬ p85) ∨ (¬ p227) ∨ (¬ p1206) ∨ (¬ p582)) : p121 ∨ (¬ p227) ∨ (¬ p582) ∨ p495 ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h24690 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)

theorem step34414 (p2 p8 p15 p63 p69 p85 p124 p224 p304 p595 p662 p710 p734 p1229 p1291 p1325 p1333 p1335 : Prop)
    (h26832 : (¬ p15) ∨ (¬ p69))
    (h26859 : p304 ∨ p124)
    (h26835 : p85 ∨ p63)
    (h26889 : p710 ∨ p8)
    (h26931 : p1333 ∨ p1325)
    (h25439 : (¬ p710) ∨ (¬ p734) ∨ (¬ p662) ∨ (¬ p224) ∨ (¬ p304) ∨ (¬ p2) ∨ (¬ p1291) ∨ (¬ p1335) ∨ (¬ p1333) ∨ (¬ p85) ∨ (¬ p595) ∨ p69 ∨ (¬ p1229)) : (¬ p2) ∨ (¬ p734) ∨ (¬ p15) ∨ (¬ p224) ∨ p124 ∨ p63 ∨ (¬ p595) ∨ (¬ p662) ∨ (¬ p1229) ∨ p8 ∨ p1325 ∨ (¬ p1335) ∨ (¬ p1291) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p662 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p1291 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))))
  have u13 : (¬ p69) := by
    rcases h26832 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u14 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u15 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u16 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  have u17 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u10 q1)
  rcases h25439 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  · exact False.elim (q0 u16)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u14)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u12)
  · exact False.elim (q7 u11)
  · exact False.elim (q8 u17)
  · exact False.elim (q9 u15)
  · exact False.elim (q10 u6)
  · exact False.elim (u13 q11)
  · exact False.elim (q12 u8)

theorem step34415 (p185 p237 p244 : Prop)
    (h26851 : p237 ∨ p185)
    (h25127 : p244 ∨ (¬ p237)) : p244 ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p244) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr hu)
  have u2 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h25127 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)

theorem step34416 (p17 p101 p134 p185 p237 : Prop)
    (h26851 : p237 ∨ p185)
    (h24808 : (¬ p17) ∨ p134 ∨ (¬ p237) ∨ (¬ p101)) : (¬ p17) ∨ (¬ p101) ∨ p185 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h24808 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)

theorem step34420 (p6 p134 p142 p163 p167 p185 p188 p189 p193 p237 : Prop)
    (h26851 : p237 ∨ p185)
    (h26842 : (¬ p163) ∨ (¬ p167))
    (h26844 : (¬ p189) ∨ (¬ p193))
    (h26841 : p142 ∨ p134)
    (h25299 : (¬ p237) ∨ p167 ∨ p193 ∨ (¬ p188) ∨ (¬ p6) ∨ (¬ p142)) : p185 ∨ (¬ p163) ∨ (¬ p189) ∨ p134 ∨ (¬ p6) ∨ (¬ p188) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p185) := fun hu => hn (Or.inl hu)
  have u1 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : (¬ p167) := by
    rcases h26842 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  have u8 : (¬ p193) := by
    rcases h26844 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u9 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h25299 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u6)
  · exact False.elim (u7 q1)
  · exact False.elim (u8 q2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u9)

theorem step34423 (p185 p237 p303 p387 p419 p961 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h26851 : p237 ∨ p185)
    (h26866 : (¬ p303) ∨ (¬ p387))
    (h24518 : (¬ p961) ∨ p387 ∨ (¬ p237) ∨ (¬ p996)) : p419 ∨ p185 ∨ (¬ p303) ∨ (¬ p961) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : (¬ p387) := by
    rcases h26866 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h24518 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step34428 (p344 p346 p351 : Prop)
    (h26862 : (¬ p344) ∨ (¬ p346))
    (h24424 : p351 ∨ p346) : p351 ∨ (¬ p344) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p351) := fun hu => hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p346) := by
    rcases h26862 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24424 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step34429 (p6 p134 p142 p224 p351 p382 p406 p424 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h26869 : p406 ∨ p382)
    (h26841 : p142 ∨ p134)
    (h25731 : (¬ p796) ∨ (¬ p351) ∨ (¬ p406) ∨ (¬ p224) ∨ (¬ p142) ∨ (¬ p6)) : p424 ∨ p382 ∨ p134 ∨ (¬ p6) ∨ (¬ p351) ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h25731 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u3)

theorem step34430 (p2 p6 p303 p382 p406 p481 : Prop)
    (h26869 : p406 ∨ p382)
    (h26873 : p481 ∨ p2)
    (h25733 : (¬ p481) ∨ (¬ p303) ∨ (¬ p406) ∨ (¬ p6)) : p382 ∨ (¬ p303) ∨ (¬ p6) ∨ p2 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h25733 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)

theorem step34432 (p6 p15 p63 p134 p142 p495 p499 : Prop)
    (h26875 : p499 ∨ p495)
    (h26841 : p142 ∨ p134)
    (h25639 : p15 ∨ (¬ p499) ∨ (¬ p6) ∨ (¬ p63) ∨ (¬ p142)) : p495 ∨ p15 ∨ (¬ p63) ∨ (¬ p6) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p495) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h25639 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)

theorem step34435 (p3 p6 p63 p163 p226 p258 p344 p346 : Prop)
    (h26863 : p346 ∨ p344)
    (h26847 : p226 ∨ p3)
    (h25648 : p63 ∨ (¬ p258) ∨ (¬ p163) ∨ (¬ p346) ∨ (¬ p6) ∨ (¬ p226)) : (¬ p258) ∨ p344 ∨ p63 ∨ (¬ p6) ∨ (¬ p163) ∨ p3 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h25648 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u7)

theorem step34436 (p2 p10 p134 p142 p192 p323 p420 p601 : Prop)
    (h26860 : (¬ p10) ∨ (¬ p323))
    (h26841 : p142 ∨ p134)
    (h26881 : p601 ∨ p420)
    (h26317 : p323 ∨ (¬ p192) ∨ (¬ p2) ∨ (¬ p142) ∨ (¬ p601)) : (¬ p2) ∨ (¬ p10) ∨ p134 ∨ p420 ∨ (¬ p192) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p323) := by
    rcases h26860 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h26317 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)

theorem step34438 (p10 p323 p326 p329 : Prop)
    (h26860 : (¬ p10) ∨ (¬ p323))
    (h25346 : p326 ∨ p323 ∨ p329) : p326 ∨ p329 ∨ (¬ p10) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p326) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p329) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p323) := by
    rcases h26860 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h25346 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (u1 q2)

theorem step34440 (p10 p125 p213 p323 p435 p687 : Prop)
    (h26860 : (¬ p10) ∨ (¬ p323))
    (h25123 : p125 ∨ (¬ p213) ∨ (¬ p687) ∨ (¬ p435) ∨ p323) : (¬ p687) ∨ (¬ p10) ∨ p125 ∨ (¬ p435) ∨ (¬ p213) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p213 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p323) := by
    rcases h26860 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h25123 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (u5 q4)

theorem step34444 (p419 p996 p998 p1005 p1012 : Prop)
    (h26904 : (¬ p419) ∨ (¬ p996))
    (h25517 : p1005 ∨ (¬ p1012) ∨ p998 ∨ p996) : p1005 ∨ p998 ∨ (¬ p1012) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1005) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p998) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1012 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p996) := by
    rcases h26904 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h25517 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u4 q3)

theorem step34445 (p419 p996 p998 p1006 p1012 : Prop)
    (h26904 : (¬ p419) ∨ (¬ p996))
    (h25518 : p1006 ∨ (¬ p1012) ∨ p998 ∨ p996) : p1006 ∨ p998 ∨ (¬ p1012) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1006) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p998) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1012 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p996) := by
    rcases h26904 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h25518 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u4 q3)

theorem step34446 (p419 p996 p998 p1007 p1012 : Prop)
    (h26904 : (¬ p419) ∨ (¬ p996))
    (h25519 : p1007 ∨ (¬ p1012) ∨ p998 ∨ p996) : p1007 ∨ p998 ∨ (¬ p1012) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1007) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p998) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1012 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p996) := by
    rcases h26904 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h25519 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u4 q3)

theorem step34447 (p419 p996 p998 p1008 p1012 : Prop)
    (h26904 : (¬ p419) ∨ (¬ p996))
    (h25520 : p1008 ∨ (¬ p1012) ∨ p998 ∨ p996) : p1008 ∨ p998 ∨ (¬ p1012) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1008) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p998) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1012 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p996) := by
    rcases h26904 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h25520 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u4 q3)

theorem step34448 (p2 p479 p481 : Prop)
    (h26872 : (¬ p2) ∨ (¬ p481))
    (h24472 : p479 ∨ p481) : p479 ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p479) := fun hu => hn (Or.inl hu)
  have u1 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p481) := by
    rcases h26872 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24472 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step34450 (p2 p3 p5 p12 p67 p124 p134 p142 p191 p207 p225 p226 p303 p368 p387 p420 p422 p495 p499 p544 p557 p601 p668 p728 p980 p1036 p1055 p1061 p1256 p1311 p1330 : Prop)
    (h26867 : p387 ∨ p303)
    (h26841 : p142 ∨ p134)
    (h26876 : (¬ p225) ∨ (¬ p544))
    (h26929 : p1256 ∨ p422)
    (h26909 : p1061 ∨ p1055)
    (h26881 : p601 ∨ p420)
    (h26875 : p499 ∨ p495)
    (h26906 : (¬ p12) ∨ (¬ p1036))
    (h26847 : p226 ∨ p3)
    (h25660 : p544 ∨ (¬ p499) ∨ (¬ p5) ∨ (¬ p601) ∨ (¬ p1311) ∨ (¬ p980) ∨ (¬ p1061) ∨ p1036 ∨ (¬ p557) ∨ (¬ p226) ∨ (¬ p67) ∨ (¬ p728) ∨ (¬ p1330) ∨ (¬ p124) ∨ (¬ p368) ∨ (¬ p207) ∨ (¬ p1256) ∨ (¬ p668) ∨ (¬ p387) ∨ (¬ p2) ∨ (¬ p142) ∨ (¬ p191)) : (¬ p2) ∨ p303 ∨ p134 ∨ (¬ p191) ∨ (¬ p225) ∨ p422 ∨ p1055 ∨ (¬ p1311) ∨ p420 ∨ (¬ p1330) ∨ (¬ p67) ∨ (¬ p980) ∨ (¬ p728) ∨ p495 ∨ (¬ p12) ∨ (¬ p207) ∨ (¬ p557) ∨ p3 ∨ (¬ p668) ∨ (¬ p368) ∨ (¬ p5) ∨ (¬ p124) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1311 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))
  have u15 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))
  have u16 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))
  have u17 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))))
  have u18 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))))
  have u19 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))))))
  have u20 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))))))
  have u21 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))))))))))))
  have u22 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u23 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u24 : (¬ p544) := by
    rcases h26876 with q0 | q1
    · exact False.elim (q0 u4)
    · exact q1
  have u25 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u26 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u27 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u28 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u13 q1)
  have u29 : (¬ p1036) := by
    rcases h26906 with q0 | q1
    · exact False.elim (q0 u14)
    · exact q1
  have u30 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u17 q1)
  rcases h25660 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14 | q15 | q16 | q17 | q18 | q19 | q20 | q21
  · exact False.elim (u24 q0)
  · exact False.elim (q1 u28)
  · exact False.elim (q2 u20)
  · exact False.elim (q3 u27)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u26)
  · exact False.elim (u29 q7)
  · exact False.elim (q8 u16)
  · exact False.elim (q9 u30)
  · exact False.elim (q10 u10)
  · exact False.elim (q11 u12)
  · exact False.elim (q12 u9)
  · exact False.elim (q13 u21)
  · exact False.elim (q14 u19)
  · exact False.elim (q15 u15)
  · exact False.elim (q16 u25)
  · exact False.elim (q17 u18)
  · exact False.elim (q18 u22)
  · exact False.elim (q19 u0)
  · exact False.elim (q20 u23)
  · exact False.elim (q21 u3)

theorem step34455 (p17 p124 p224 p304 p344 p346 p836 p840 : Prop)
    (h26859 : p304 ∨ p124)
    (h26863 : p346 ∨ p344)
    (h26895 : p840 ∨ p836)
    (h24770 : (¬ p346) ∨ (¬ p224) ∨ (¬ p840) ∨ (¬ p304) ∨ (¬ p17)) : p124 ∨ p344 ∨ p836 ∨ (¬ p17) ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p224 := by
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
  have u7 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h24770 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)

theorem step34456 (p124 p189 p193 p258 p304 : Prop)
    (h26859 : p304 ∨ p124)
    (h26845 : p193 ∨ p189)
    (h25550 : p258 ∨ (¬ p304) ∨ (¬ p193)) : p124 ∨ p189 ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h25550 with q0 | q1 | q2
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)

theorem step34457 (p41 p45 p87 p124 p304 p576 p581 p633 : Prop)
    (h26879 : p581 ∨ p576)
    (h26831 : p45 ∨ p41)
    (h26859 : p304 ∨ p124)
    (h25318 : (¬ p633) ∨ (¬ p304) ∨ (¬ p87) ∨ (¬ p45) ∨ (¬ p581)) : p576 ∨ p41 ∨ (¬ p633) ∨ (¬ p87) ∨ p124 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p576) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p41) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h25318 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step34459 (p3 p124 p125 p190 p225 p239 p304 p305 p348 p350 p362 p663 p789 p790 p814 p858 p1325 : Prop)
    (h26897 : p858 ∨ p789)
    (h26865 : p362 ∨ p125)
    (h26859 : p304 ∨ p124)
    (h26893 : p814 ∨ p790)
    (h25206 : (¬ p1325) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p3) ∨ (¬ p239) ∨ (¬ p190) ∨ (¬ p663) ∨ p225 ∨ (¬ p348) ∨ (¬ p305) ∨ (¬ p304) ∨ (¬ p350) ∨ (¬ p362)) : (¬ p305) ∨ (¬ p190) ∨ p789 ∨ (¬ p348) ∨ (¬ p1325) ∨ (¬ p239) ∨ p125 ∨ p225 ∨ (¬ p3) ∨ (¬ p350) ∨ p124 ∨ p790 ∨ (¬ p663) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p239 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p663 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))))
  have u13 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u14 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u15 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u10 q1)
  have u16 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  rcases h25206 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u16)
  · exact False.elim (q2 u13)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u12)
  · exact False.elim (u7 q7)
  · exact False.elim (q8 u3)
  · exact False.elim (q9 u0)
  · exact False.elim (q10 u15)
  · exact False.elim (q11 u9)
  · exact False.elim (q12 u14)

theorem step34460 (p10 p103 p124 p125 p169 p185 p189 p225 p237 p242 p304 p323 p544 p940 : Prop)
    (h26859 : p304 ∨ p124)
    (h26877 : p544 ∨ p225)
    (h26851 : p237 ∨ p185)
    (h26861 : p323 ∨ p10)
    (h24788 : (¬ p940) ∨ (¬ p242) ∨ (¬ p189) ∨ (¬ p237) ∨ (¬ p103) ∨ (¬ p169) ∨ (¬ p323) ∨ p125 ∨ (¬ p544) ∨ p225 ∨ (¬ p304)) : (¬ p103) ∨ p124 ∨ p225 ∨ (¬ p940) ∨ p125 ∨ p185 ∨ (¬ p242) ∨ (¬ p189) ∨ (¬ p169) ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p169 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u11 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u12 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u13 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h24788 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u12)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u13)
  · exact False.elim (u4 q7)
  · exact False.elim (q8 u11)
  · exact False.elim (u2 q9)
  · exact False.elim (q10 u10)

theorem step34465 (p3 p41 p47 p63 p124 p134 p142 p163 p167 p195 p304 p424 p543 p789 p796 p836 p840 p858 p918 : Prop)
    (h26859 : p304 ∨ p124)
    (h26895 : p840 ∨ p836)
    (h26843 : p167 ∨ p163)
    (h26897 : p858 ∨ p789)
    (h26841 : p142 ∨ p134)
    (h26890 : (¬ p424) ∨ (¬ p796))
    (h25542 : p796 ∨ (¬ p858) ∨ (¬ p304) ∨ (¬ p47) ∨ (¬ p41) ∨ (¬ p167) ∨ p918 ∨ (¬ p142) ∨ (¬ p840) ∨ (¬ p195) ∨ (¬ p3) ∨ (¬ p543) ∨ (¬ p63)) : p124 ∨ (¬ p3) ∨ p836 ∨ (¬ p63) ∨ p163 ∨ (¬ p41) ∨ (¬ p47) ∨ p789 ∨ p918 ∨ (¬ p195) ∨ p134 ∨ (¬ p424) ∨ (¬ p543) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p543 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))))
  have u13 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u14 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u15 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u16 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u17 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u10 q1)
  have u18 : (¬ p796) := by
    rcases h26890 with q0 | q1
    · exact False.elim (q0 u11)
    · exact q1
  rcases h25542 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  · exact False.elim (u18 q0)
  · exact False.elim (q1 u16)
  · exact False.elim (q2 u13)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u15)
  · exact False.elim (u8 q6)
  · exact False.elim (q7 u17)
  · exact False.elim (q8 u14)
  · exact False.elim (q9 u9)
  · exact False.elim (q10 u1)
  · exact False.elim (q11 u12)
  · exact False.elim (q12 u3)

theorem step34466 (p3 p63 p124 p163 p167 p195 p225 p304 p544 p918 p928 p1035 : Prop)
    (h26901 : p928 ∨ p918)
    (h26843 : p167 ∨ p163)
    (h26877 : p544 ∨ p225)
    (h26859 : p304 ∨ p124)
    (h25555 : (¬ p1035) ∨ (¬ p304) ∨ (¬ p167) ∨ (¬ p928) ∨ (¬ p195) ∨ (¬ p3) ∨ (¬ p544) ∨ (¬ p63)) : (¬ p1035) ∨ p918 ∨ (¬ p3) ∨ p163 ∨ (¬ p195) ∨ (¬ p63) ∨ p225 ∨ p124 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h25555 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u11)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u5)

theorem step34470 (p10 p17 p41 p189 p193 p256 p323 : Prop)
    (h26853 : p256 ∨ p17)
    (h26861 : p323 ∨ p10)
    (h26844 : (¬ p189) ∨ (¬ p193))
    (h25674 : p193 ∨ (¬ p256) ∨ (¬ p41) ∨ (¬ p323)) : p17 ∨ (¬ p41) ∨ p10 ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p17) := fun hu => hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : (¬ p193) := by
    rcases h26844 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h25674 with q0 | q1 | q2 | q3
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)

theorem step34472 (p5 p6 p17 p101 p156 p185 p192 p237 p256 p351 p382 p406 p595 p790 p814 p897 p904 p1084 p1096 p1286 : Prop)
    (h26850 : (¬ p185) ∨ (¬ p237))
    (h26893 : p814 ∨ p790)
    (h26853 : p256 ∨ p17)
    (h26899 : p904 ∨ p897)
    (h26869 : p406 ∨ p382)
    (h25699 : (¬ p256) ∨ (¬ p1286) ∨ (¬ p904) ∨ (¬ p351) ∨ (¬ p1096) ∨ (¬ p1084) ∨ (¬ p5) ∨ (¬ p595) ∨ (¬ p101) ∨ (¬ p6) ∨ (¬ p156) ∨ p237 ∨ (¬ p814) ∨ (¬ p406) ∨ (¬ p192)) : (¬ p1096) ∨ (¬ p101) ∨ (¬ p192) ∨ (¬ p351) ∨ (¬ p185) ∨ (¬ p1084) ∨ (¬ p156) ∨ p790 ∨ (¬ p5) ∨ (¬ p1286) ∨ p17 ∨ (¬ p6) ∨ p897 ∨ (¬ p595) ∨ p382 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
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
  have u3 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))))))
  have u15 : (¬ p237) := by
    rcases h26850 with q0 | q1
    · exact False.elim (q0 u4)
    · exact q1
  have u16 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u17 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u10 q1)
  have u18 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u12 q1)
  have u19 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u14 q1)
  rcases h25699 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14
  · exact False.elim (q0 u17)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u18)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u13)
  · exact False.elim (q8 u1)
  · exact False.elim (q9 u11)
  · exact False.elim (q10 u6)
  · exact False.elim (u15 q11)
  · exact False.elim (q12 u16)
  · exact False.elim (q13 u19)
  · exact False.elim (q14 u2)

theorem step34473 (p17 p189 p256 p303 p382 p387 p406 p789 p858 : Prop)
    (h26867 : p387 ∨ p303)
    (h26853 : p256 ∨ p17)
    (h26897 : p858 ∨ p789)
    (h26869 : p406 ∨ p382)
    (h25557 : (¬ p858) ∨ (¬ p387) ∨ (¬ p256) ∨ (¬ p406) ∨ (¬ p189)) : p303 ∨ p17 ∨ p789 ∨ (¬ p189) ∨ p382 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h25557 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u3)

theorem step34474 (p17 p90 p224 p256 p258 p287 p288 p574 p633 p657 p918 p1076 p1077 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26887 : p657 ∨ p224)
    (h26586 : p90)
    (h26855 : p288 ∨ p258)
    (h26853 : p256 ∨ p17)
    (h25678 : (¬ p657) ∨ (¬ p633) ∨ (¬ p90) ∨ (¬ p918) ∨ (¬ p574) ∨ (¬ p288) ∨ (¬ p287) ∨ (¬ p256) ∨ (¬ p1077)) : p1076 ∨ p224 ∨ (¬ p918) ∨ p258 ∨ (¬ p574) ∨ p17 ∨ (¬ p633) ∨ (¬ p287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1076) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p574 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p90 := by
    exact h26586
  have u11 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u12 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h25678 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u12)
  · exact False.elim (q8 u8)

theorem step34483 (p8 p15 p595 p710 p1096 p1099 p1229 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26889 : p710 ∨ p8)
    (h25412 : (¬ p1099) ∨ (¬ p15) ∨ (¬ p595) ∨ (¬ p1229) ∨ (¬ p710)) : p1096 ∨ p8 ∨ (¬ p595) ∨ (¬ p1229) ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1096) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p8) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h25412 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)

theorem step34484 (p41 p45 p63 p85 p163 p1096 p1099 : Prop)
    (h26830 : (¬ p41) ∨ (¬ p45))
    (h26834 : (¬ p63) ∨ (¬ p85))
    (h26913 : p1099 ∨ p1096)
    (h24465 : p85 ∨ p45 ∨ p163 ∨ (¬ p1099)) : p163 ∨ (¬ p41) ∨ (¬ p63) ∨ p1096 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p163) := fun hu => hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p45) := by
    rcases h26830 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  have u5 : (¬ p85) := by
    rcases h26834 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u6 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h24465 with q0 | q1 | q2 | q3
  · exact False.elim (u5 q0)
  · exact False.elim (u4 q1)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u6)

theorem step34485 (p495 p499 p633 p1055 p1096 p1099 p1229 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26875 : p499 ∨ p495)
    (h25394 : (¬ p1099) ∨ (¬ p1229) ∨ (¬ p1055) ∨ p633 ∨ (¬ p499)) : p633 ∨ p1096 ∨ (¬ p1229) ∨ p495 ∨ (¬ p1055) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h25394 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u6)

theorem step34487 (p12 p14 p229 p560 p1055 p1115 p1116 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h26849 : p229 ∨ p14)
    (h25154 : (¬ p1116) ∨ (¬ p1055) ∨ p12 ∨ (¬ p229) ∨ (¬ p560)) : (¬ p560) ∨ p12 ∨ (¬ p1055) ∨ p1115 ∨ p14 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h25154 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u0)

theorem step34488 (p163 p189 p193 p1055 p1115 p1116 : Prop)
    (h26845 : p193 ∨ p189)
    (h26915 : p1116 ∨ p1115)
    (h25613 : (¬ p1116) ∨ p163 ∨ (¬ p193) ∨ (¬ p1055)) : (¬ p1055) ∨ p189 ∨ p163 ∨ p1115 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h25613 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step34489 (p105 p134 p142 p163 p185 p189 p193 : Prop)
    (h26845 : p193 ∨ p189)
    (h26841 : p142 ∨ p134)
    (h24398 : (¬ p185) ∨ (¬ p142) ∨ (¬ p105) ∨ p163 ∨ (¬ p193)) : p189 ∨ (¬ p185) ∨ (¬ p105) ∨ p134 ∨ p163 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p189) := fun hu => hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h24398 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (u4 q3)
  · exact False.elim (q4 u5)

theorem step34499 (p101 p102 p106 p107 : Prop)
    (h26836 : (¬ p101) ∨ (¬ p102))
    (h24729 : p106 ∨ p107 ∨ p102) : p106 ∨ p107 ∨ (¬ p101) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p106) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p107) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p102) := by
    rcases h26836 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h24729 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (u3 q2)

theorem step34500 (p224 p303 p348 p657 p727 p789 p836 p1584 : Prop)
    (h26886 : (¬ p224) ∨ (¬ p657))
    (h25745 : (¬ p789) ∨ (¬ p1584) ∨ (¬ p303) ∨ (¬ p727) ∨ (¬ p348) ∨ p836 ∨ p657) : (¬ p1584) ∨ (¬ p727) ∨ (¬ p224) ∨ (¬ p303) ∨ (¬ p348) ∨ (¬ p789) ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p727 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
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
  have u5 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p657) := by
    rcases h26886 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h25745 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)
  · exact False.elim (u6 q5)
  · exact False.elim (u7 q6)

theorem step34505 (p11 p258 p1115 p1116 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h24771 : p258 ∨ (¬ p1116) ∨ (¬ p11)) : (¬ p11) ∨ p1115 ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1115) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h24771 with q0 | q1 | q2
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)

theorem step34510 (p126 p303 p789 p858 p1325 p1452 : Prop)
    (h26897 : p858 ∨ p789)
    (h24593 : (¬ p858) ∨ (¬ p1325) ∨ (¬ p1452) ∨ p303 ∨ p126) : (¬ p1452) ∨ p126 ∨ (¬ p1325) ∨ p303 ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h24593 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (u3 q3)
  · exact False.elim (u1 q4)

theorem step34511 (p16 p189 p224 p287 p303 p344 p382 p406 p495 p499 p633 p657 p680 p727 p769 p836 p1325 : Prop)
    (h26869 : p406 ∨ p382)
    (h26875 : p499 ∨ p495)
    (h26886 : (¬ p224) ∨ (¬ p657))
    (h25746 : (¬ p406) ∨ (¬ p1325) ∨ (¬ p769) ∨ (¬ p303) ∨ (¬ p680) ∨ (¬ p727) ∨ (¬ p189) ∨ p836 ∨ (¬ p344) ∨ p657 ∨ (¬ p16) ∨ (¬ p287) ∨ (¬ p633) ∨ (¬ p499)) : (¬ p344) ∨ (¬ p633) ∨ p382 ∨ (¬ p1325) ∨ p495 ∨ (¬ p727) ∨ (¬ p189) ∨ p836 ∨ (¬ p680) ∨ (¬ p224) ∨ (¬ p16) ∨ (¬ p303) ∨ (¬ p769) ∨ (¬ p287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p727 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p769 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : p287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))))
  have u14 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u15 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u16 : (¬ p657) := by
    rcases h26886 with q0 | q1
    · exact False.elim (q0 u9)
    · exact q1
  rcases h25746 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13
  · exact False.elim (q0 u14)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u12)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)
  · exact False.elim (u7 q7)
  · exact False.elim (q8 u0)
  · exact False.elim (u16 q9)
  · exact False.elim (q10 u10)
  · exact False.elim (q11 u13)
  · exact False.elim (q12 u1)
  · exact False.elim (q13 u15)

theorem step34512 (p6 p10 p15 p127 p303 p323 p387 p495 p499 : Prop)
    (h26875 : p499 ∨ p495)
    (h26867 : p387 ∨ p303)
    (h26839 : p127 ∨ p6)
    (h26861 : p323 ∨ p10)
    (h25204 : p15 ∨ (¬ p499) ∨ (¬ p387) ∨ (¬ p323) ∨ (¬ p127)) : p495 ∨ p303 ∨ p15 ∨ p6 ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p495) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h25204 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u7)

theorem step34518 (p12 p134 p163 p167 p195 p210 p305 p344 p346 p756 p940 p1036 : Prop)
    (h26843 : p167 ∨ p163)
    (h26863 : p346 ∨ p344)
    (h26907 : p1036 ∨ p12)
    (h25170 : (¬ p346) ∨ (¬ p167) ∨ (¬ p210) ∨ (¬ p134) ∨ (¬ p1036) ∨ (¬ p940) ∨ (¬ p195) ∨ (¬ p756) ∨ (¬ p305)) : (¬ p940) ∨ (¬ p756) ∨ p163 ∨ p344 ∨ (¬ p134) ∨ p12 ∨ (¬ p195) ∨ (¬ p210) ∨ (¬ p305) := by
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
  have u2 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h25170 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u8)

theorem step34522 (p979 p980 p983 : Prop)
    (h26902 : (¬ p980) ∨ (¬ p983))
    (h24405 : p979 ∨ p983) : p979 ∨ (¬ p980) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p979) := fun hu => hn (Or.inl hu)
  have u1 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p983) := by
    rcases h26902 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24405 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step34533 (p101 p102 p125 p227 p324 p383 p419 p435 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h26837 : p102 ∨ p101)
    (h24919 : (¬ p435) ∨ (¬ p102) ∨ (¬ p125) ∨ (¬ p996) ∨ (¬ p227) ∨ (¬ p383) ∨ (¬ p324)) : (¬ p324) ∨ (¬ p383) ∨ (¬ p227) ∨ (¬ p125) ∨ p419 ∨ p101 ∨ (¬ p435) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p324 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p383 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u8 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h24919 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u0)

theorem step34534 (p3 p11 p12 p15 p69 p125 p126 p495 p499 : Prop)
    (h26833 : p69 ∨ p15)
    (h26875 : p499 ∨ p495)
    (h24713 : (¬ p499) ∨ (¬ p12) ∨ (¬ p11) ∨ (¬ p126) ∨ (¬ p125) ∨ (¬ p3) ∨ (¬ p69)) : (¬ p11) ∨ (¬ p12) ∨ (¬ p3) ∨ p15 ∨ (¬ p126) ∨ p495 ∨ (¬ p125) := by
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
  have u2 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h24713 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u7)

theorem step34541 (p17 p63 p101 p102 p121 p455 p576 p581 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26879 : p581 ∨ p576)
    (h26837 : p102 ∨ p101)
    (h25313 : (¬ p455) ∨ (¬ p1206) ∨ (¬ p102) ∨ (¬ p581) ∨ p63 ∨ (¬ p17)) : p121 ∨ p576 ∨ p101 ∨ (¬ p17) ∨ p63 ∨ (¬ p455) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h25313 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u7)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u3)

theorem step34553 (p3 p101 p163 p167 p258 : Prop)
    (h26843 : p167 ∨ p163)
    (h25144 : p101 ∨ (¬ p167) ∨ (¬ p3) ∨ (¬ p258)) : (¬ p3) ∨ p101 ∨ p163 ∨ (¬ p258) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p101) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h25144 with q0 | q1 | q2 | q3
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)

theorem step34554 (p3 p101 p102 p107 p163 p167 p258 : Prop)
    (h26837 : p102 ∨ p101)
    (h26843 : p167 ∨ p163)
    (h25140 : (¬ p3) ∨ (¬ p167) ∨ (¬ p107) ∨ (¬ p102) ∨ (¬ p258)) : p101 ∨ (¬ p258) ∨ p163 ∨ (¬ p107) ∨ (¬ p3) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p101) := fun hu => hn (Or.inl hu)
  have u1 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p107 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h25140 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)

theorem step34555 (p17 p126 p258 p301 p790 : Prop)
    (h26856 : (¬ p126) ∨ (¬ p301))
    (h25565 : p301 ∨ (¬ p258) ∨ (¬ p790) ∨ (¬ p17)) : (¬ p17) ∨ (¬ p258) ∨ (¬ p790) ∨ (¬ p126) := by
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
  have u2 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p301) := by
    rcases h26856 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h25565 with q0 | q1 | q2 | q3
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)

theorem step34563 (p12 p225 p734 p1036 : Prop)
    (h26906 : (¬ p12) ∨ (¬ p1036))
    (h24586 : p1036 ∨ (¬ p225) ∨ (¬ p734)) : (¬ p12) ∨ (¬ p225) ∨ (¬ p734) := by
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
  have u2 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1036) := by
    rcases h26906 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h24586 with q0 | q1 | q2
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)

theorem step34565 (p6 p12 p14 p16 p18 p126 p134 p140 p142 p185 p229 p255 p258 p301 p308 p419 p422 p556 p557 p879 p1036 p1076 p1077 p1096 p1164 p1229 p1256 : Prop)
    (h26907 : p1036 ∨ p12)
    (h26911 : p1077 ∨ p1076)
    (h26857 : p301 ∨ p126)
    (h26929 : p1256 ∨ p422)
    (h26849 : p229 ∨ p14)
    (h26841 : p142 ∨ p134)
    (h25630 : (¬ p419) ∨ (¬ p1229) ∨ (¬ p301) ∨ (¬ p1164) ∨ (¬ p1256) ∨ (¬ p1096) ∨ (¬ p1036) ∨ (¬ p1077) ∨ (¬ p879) ∨ (¬ p556) ∨ (¬ p557) ∨ (¬ p229) ∨ (¬ p185) ∨ (¬ p255) ∨ (¬ p258) ∨ (¬ p308) ∨ (¬ p16) ∨ (¬ p140) ∨ (¬ p142) ∨ (¬ p18) ∨ (¬ p6)) : p12 ∨ p1076 ∨ p126 ∨ (¬ p255) ∨ (¬ p18) ∨ (¬ p1096) ∨ p422 ∨ (¬ p1229) ∨ (¬ p6) ∨ (¬ p556) ∨ (¬ p557) ∨ p14 ∨ (¬ p185) ∨ (¬ p1164) ∨ (¬ p419) ∨ (¬ p308) ∨ (¬ p16) ∨ (¬ p879) ∨ p134 ∨ (¬ p140) ∨ (¬ p258) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p12) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p126) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p255 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p556 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : p1164 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))
  have u15 : p308 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))
  have u16 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))
  have u17 : p879 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))))
  have u18 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))))
  have u19 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))))))
  have u20 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))))))))))))
  have u21 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u22 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u23 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u24 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u25 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  have u26 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u18 q1)
  rcases h25630 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14 | q15 | q16 | q17 | q18 | q19 | q20
  · exact False.elim (q0 u14)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u23)
  · exact False.elim (q3 u13)
  · exact False.elim (q4 u24)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u21)
  · exact False.elim (q7 u22)
  · exact False.elim (q8 u17)
  · exact False.elim (q9 u9)
  · exact False.elim (q10 u10)
  · exact False.elim (q11 u25)
  · exact False.elim (q12 u12)
  · exact False.elim (q13 u3)
  · exact False.elim (q14 u20)
  · exact False.elim (q15 u15)
  · exact False.elim (q16 u16)
  · exact False.elim (q17 u19)
  · exact False.elim (q18 u26)
  · exact False.elim (q19 u4)
  · exact False.elim (q20 u8)

theorem step34574 (p2 p6 p12 p134 p163 p189 p193 p328 p481 p1076 p1077 : Prop)
    (h26845 : p193 ∨ p189)
    (h26911 : p1077 ∨ p1076)
    (h26873 : p481 ∨ p2)
    (h25679 : (¬ p481) ∨ (¬ p6) ∨ (¬ p163) ∨ (¬ p12) ∨ (¬ p1077) ∨ (¬ p134) ∨ (¬ p193) ∨ (¬ p328)) : p189 ∨ p1076 ∨ (¬ p6) ∨ p2 ∨ (¬ p12) ∨ (¬ p134) ∨ (¬ p163) ∨ (¬ p328) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p189) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p328 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h25679 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u7)

theorem step34577 (p790 p814 p820 : Prop)
    (h26892 : (¬ p790) ∨ (¬ p814))
    (h24495 : p820 ∨ p814) : p820 ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p820) := fun hu => hn (Or.inl hu)
  have u1 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p814) := by
    rcases h26892 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24495 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step34578 (p790 p814 p821 : Prop)
    (h26892 : (¬ p790) ∨ (¬ p814))
    (h24527 : p821 ∨ p814) : p821 ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p821) := fun hu => hn (Or.inl hu)
  have u1 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p814) := by
    rcases h26892 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24527 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step34585 (p5 p6 p89 p101 p192 p344 p346 p790 p1385 : Prop)
    (h26863 : p346 ∨ p344)
    (h25687 : (¬ p6) ∨ (¬ p5) ∨ (¬ p89) ∨ (¬ p1385) ∨ (¬ p790) ∨ (¬ p101) ∨ (¬ p346) ∨ (¬ p192)) : (¬ p101) ∨ p344 ∨ (¬ p5) ∨ (¬ p790) ∨ (¬ p192) ∨ (¬ p6) ∨ (¬ p89) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p89 := by
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
  rcases h25687 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u4)

theorem step34591 (p2 p195 p382 p406 p424 p789 p858 : Prop)
    (h26869 : p406 ∨ p382)
    (h26897 : p858 ∨ p789)
    (h25175 : p424 ∨ (¬ p858) ∨ (¬ p195) ∨ p2 ∨ (¬ p406)) : p424 ∨ p382 ∨ (¬ p195) ∨ p2 ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h25175 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u5)

theorem step34592 (p3 p14 p72 p229 p234 p480 p665 p789 p790 p858 p880 p997 p1015 p1042 p1095 p1096 p1187 p1325 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26849 : p229 ∨ p14)
    (h26897 : p858 ∨ p789)
    (h25209 : (¬ p3) ∨ p1325 ∨ p790 ∨ (¬ p1015) ∨ (¬ p858) ∨ (¬ p1095) ∨ (¬ p1042) ∨ (¬ p997) ∨ (¬ p665) ∨ (¬ p1096) ∨ (¬ p229) ∨ (¬ p880) ∨ (¬ p1187) ∨ (¬ p72) ∨ (¬ p480)) : p234 ∨ (¬ p880) ∨ (¬ p72) ∨ (¬ p1015) ∨ (¬ p3) ∨ p1325 ∨ p14 ∨ (¬ p480) ∨ (¬ p1096) ∨ (¬ p665) ∨ (¬ p997) ∨ (¬ p1095) ∨ p789 ∨ p790 ∨ (¬ p1042) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : p880 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p480 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p997 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : p1042 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))))))
  have u15 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u16 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u17 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u12 q1)
  rcases h25209 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14
  · exact False.elim (q0 u4)
  · exact False.elim (u5 q1)
  · exact False.elim (u13 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u17)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u14)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u9)
  · exact False.elim (q9 u8)
  · exact False.elim (q10 u16)
  · exact False.elim (q11 u1)
  · exact False.elim (q12 u15)
  · exact False.elim (q13 u2)
  · exact False.elim (q14 u7)

theorem step34593 (p3 p6 p9 p12 p16 p17 p20 p126 p134 p140 p141 p142 p163 p167 p206 p207 p344 p346 p420 p422 p601 p789 p858 p879 p1036 p1096 p1188 p1229 p1256 p1388 : Prop)
    (h26929 : p1256 ∨ p422)
    (h26907 : p1036 ∨ p12)
    (h26841 : p142 ∨ p134)
    (h26842 : (¬ p163) ∨ (¬ p167))
    (h26863 : p346 ∨ p344)
    (h26880 : (¬ p420) ∨ (¬ p601))
    (h26897 : p858 ∨ p789)
    (h25632 : (¬ p858) ∨ (¬ p1188) ∨ (¬ p207) ∨ (¬ p6) ∨ (¬ p206) ∨ (¬ p140) ∨ (¬ p141) ∨ (¬ p142) ∨ p167 ∨ (¬ p346) ∨ (¬ p9) ∨ (¬ p1096) ∨ (¬ p1229) ∨ (¬ p1256) ∨ (¬ p1388) ∨ p601 ∨ (¬ p17) ∨ (¬ p879) ∨ (¬ p20) ∨ p126 ∨ (¬ p1036) ∨ p3 ∨ (¬ p16)) : (¬ p1229) ∨ p422 ∨ (¬ p207) ∨ (¬ p6) ∨ (¬ p206) ∨ p12 ∨ (¬ p879) ∨ p134 ∨ (¬ p140) ∨ (¬ p163) ∨ (¬ p141) ∨ (¬ p1096) ∨ (¬ p9) ∨ (¬ p17) ∨ p3 ∨ p344 ∨ (¬ p420) ∨ (¬ p1388) ∨ (¬ p1188) ∨ (¬ p20) ∨ p126 ∨ p789 ∨ (¬ p16) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p422) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p879 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p9 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))
  have u15 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))
  have u16 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))
  have u17 : p1388 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))))
  have u18 : p1188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))))
  have u19 : p20 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))))))
  have u20 : (¬ p126) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))))))
  have u21 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))))))))
  have u22 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))))))))))))))
  have u23 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u24 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u25 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u26 : (¬ p167) := by
    rcases h26842 with q0 | q1
    · exact False.elim (q0 u9)
    · exact q1
  have u27 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u15 q1)
  have u28 : (¬ p601) := by
    rcases h26880 with q0 | q1
    · exact False.elim (q0 u16)
    · exact q1
  have u29 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u21 q1)
  rcases h25632 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14 | q15 | q16 | q17 | q18 | q19 | q20 | q21 | q22
  · exact False.elim (q0 u29)
  · exact False.elim (q1 u18)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u25)
  · exact False.elim (u26 q8)
  · exact False.elim (q9 u27)
  · exact False.elim (q10 u12)
  · exact False.elim (q11 u11)
  · exact False.elim (q12 u0)
  · exact False.elim (q13 u23)
  · exact False.elim (q14 u17)
  · exact False.elim (u28 q15)
  · exact False.elim (q16 u13)
  · exact False.elim (q17 u6)
  · exact False.elim (q18 u19)
  · exact False.elim (u20 q19)
  · exact False.elim (q20 u24)
  · exact False.elim (u14 q21)
  · exact False.elim (q22 u22)

theorem step34594 (p1229 p1232 p1237 : Prop)
    (h26926 : (¬ p1229) ∨ (¬ p1232))
    (h24606 : p1237 ∨ p1232) : p1237 ∨ (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1237) := fun hu => hn (Or.inl hu)
  have u1 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1232) := by
    rcases h26926 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24606 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step34604 (p5 p6 p41 p101 p156 p189 p193 p238 p557 p726 p922 p940 p1096 p1115 p1116 p1584 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h26845 : p193 ∨ p189)
    (h25689 : (¬ p1116) ∨ (¬ p726) ∨ (¬ p940) ∨ (¬ p1584) ∨ (¬ p5) ∨ (¬ p1096) ∨ (¬ p41) ∨ (¬ p101) ∨ (¬ p6) ∨ (¬ p557) ∨ (¬ p156) ∨ (¬ p193) ∨ (¬ p922) ∨ (¬ p238)) : (¬ p101) ∨ (¬ p726) ∨ (¬ p238) ∨ p1115 ∨ (¬ p156) ∨ (¬ p1096) ∨ (¬ p5) ∨ (¬ p557) ∨ (¬ p940) ∨ (¬ p1584) ∨ (¬ p41) ∨ (¬ p6) ∨ p189 ∨ (¬ p922) := by
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
  have u2 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : p922 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))))
  have u14 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u15 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u12 q1)
  rcases h25689 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13
  · exact False.elim (q0 u14)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u0)
  · exact False.elim (q8 u11)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u4)
  · exact False.elim (q11 u15)
  · exact False.elim (q12 u13)
  · exact False.elim (q13 u2)

theorem step34612 (p6 p127 p209 p210 : Prop)
    (h26838 : (¬ p6) ∨ (¬ p127))
    (h25239 : p209 ∨ p210 ∨ p127) : p209 ∨ p210 ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p209) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p210) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p127) := by
    rcases h26838 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h25239 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (u3 q2)

theorem step34614 (p105 p134 p142 p163 p167 p192 p556 p1055 p1076 p1077 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26843 : p167 ∨ p163)
    (h26841 : p142 ∨ p134)
    (h25616 : (¬ p142) ∨ (¬ p105) ∨ (¬ p1077) ∨ (¬ p556) ∨ (¬ p167) ∨ (¬ p192) ∨ (¬ p1055)) : (¬ p1055) ∨ (¬ p556) ∨ (¬ p105) ∨ p1076 ∨ (¬ p192) ∨ p163 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p556 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u9 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h25616 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u0)

theorem step34615 (p41 p45 p105 p163 p167 p576 : Prop)
    (h26831 : p45 ∨ p41)
    (h26843 : p167 ∨ p163)
    (h25615 : (¬ p45) ∨ p576 ∨ (¬ p105) ∨ (¬ p167)) : p41 ∨ p576 ∨ p163 ∨ (¬ p105) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p41) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h25615 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)

theorem step34619 (p5 p6 p41 p101 p185 p189 p193 p237 p595 p789 p1076 : Prop)
    (h26850 : (¬ p185) ∨ (¬ p237))
    (h26845 : p193 ∨ p189)
    (h25698 : (¬ p1076) ∨ (¬ p5) ∨ (¬ p595) ∨ (¬ p41) ∨ (¬ p101) ∨ (¬ p6) ∨ p237 ∨ (¬ p789) ∨ (¬ p193)) : (¬ p185) ∨ (¬ p101) ∨ (¬ p5) ∨ (¬ p789) ∨ p189 ∨ (¬ p595) ∨ (¬ p1076) ∨ (¬ p41) ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p237) := by
    rcases h26850 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u10 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h25698 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u8)
  · exact False.elim (u9 q6)
  · exact False.elim (q7 u3)
  · exact False.elim (q8 u10)

theorem step34634 (p15 p63 p83 p85 p1273 p1349 : Prop)
    (h26835 : p85 ∨ p63)
    (h25707 : (¬ p15) ∨ (¬ p1349) ∨ (¬ p83) ∨ (¬ p85) ∨ (¬ p1273)) : (¬ p15) ∨ (¬ p1273) ∨ (¬ p83) ∨ p63 ∨ (¬ p1349) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h25707 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)

theorem step34635 (p15 p41 p45 p69 p595 p616 p1385 : Prop)
    (h26833 : p69 ∨ p15)
    (h26882 : (¬ p595) ∨ (¬ p616))
    (h26831 : p45 ∨ p41)
    (h24703 : p1385 ∨ (¬ p45) ∨ (¬ p69) ∨ p616) : p1385 ∨ p15 ∨ (¬ p595) ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1385) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : (¬ p616) := by
    rcases h26882 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u6 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h24703 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (u5 q3)

theorem step34636 (p6 p14 p63 p83 p85 p101 p104 p166 p185 p229 p344 p346 p1121 p1273 : Prop)
    (h26849 : p229 ∨ p14)
    (h26835 : p85 ∨ p63)
    (h26863 : p346 ∨ p344)
    (h25705 : (¬ p346) ∨ (¬ p83) ∨ (¬ p85) ∨ (¬ p1273) ∨ (¬ p229) ∨ (¬ p1121) ∨ (¬ p185) ∨ (¬ p166) ∨ (¬ p104) ∨ (¬ p101) ∨ (¬ p6)) : (¬ p101) ∨ (¬ p166) ∨ p14 ∨ (¬ p6) ∨ (¬ p104) ∨ p63 ∨ (¬ p185) ∨ (¬ p83) ∨ (¬ p1121) ∨ p344 ∨ (¬ p1273) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p166 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u12 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u13 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h25705 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u13)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u12)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u4)
  · exact False.elim (q9 u0)
  · exact False.elim (q10 u3)

theorem step34638 (p8 p63 p85 p710 p897 p904 p1096 p1097 p1099 : Prop)
    (h26899 : p904 ∨ p897)
    (h26834 : (¬ p63) ∨ (¬ p85))
    (h26889 : p710 ∨ p8)
    (h26913 : p1099 ∨ p1096)
    (h25380 : p85 ∨ (¬ p710) ∨ (¬ p1097) ∨ (¬ p1099) ∨ (¬ p904)) : p897 ∨ (¬ p1097) ∨ (¬ p63) ∨ p8 ∨ p1096 := by
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
  have u3 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : (¬ p85) := by
    rcases h26834 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u7 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h25380 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u5)

theorem step34657 (p163 p165 p167 p171 : Prop)
    (h26842 : (¬ p163) ∨ (¬ p167))
    (h24823 : p171 ∨ p167 ∨ p165) : p171 ∨ p165 ∨ (¬ p163) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p171) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p165) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p167) := by
    rcases h26842 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h24823 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (u1 q2)

theorem step34681 (p101 p102 p106 p115 p120 : Prop)
    (h26836 : (¬ p101) ∨ (¬ p102))
    (h24725 : p115 ∨ (¬ p120) ∨ p106 ∨ p102) : p115 ∨ (¬ p120) ∨ p106 ∨ (¬ p101) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p115) := fun hu => hn (Or.inl hu)
  have u1 : p120 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p106) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p102) := by
    rcases h26836 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h24725 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (u2 q2)
  · exact False.elim (u4 q3)

theorem step34682 (p101 p102 p106 p111 p120 : Prop)
    (h26836 : (¬ p101) ∨ (¬ p102))
    (h24726 : p111 ∨ (¬ p120) ∨ p106 ∨ p102) : p111 ∨ (¬ p120) ∨ p106 ∨ (¬ p101) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p111) := fun hu => hn (Or.inl hu)
  have u1 : p120 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p106) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p102) := by
    rcases h26836 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h24726 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (u2 q2)
  · exact False.elim (u4 q3)

theorem step34683 (p101 p102 p106 p112 p120 : Prop)
    (h26836 : (¬ p101) ∨ (¬ p102))
    (h24727 : p112 ∨ (¬ p120) ∨ p106 ∨ p102) : p112 ∨ (¬ p120) ∨ p106 ∨ (¬ p101) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p112) := fun hu => hn (Or.inl hu)
  have u1 : p120 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p106) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p102) := by
    rcases h26836 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h24727 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (u2 q2)
  · exact False.elim (u4 q3)

theorem step34684 (p101 p102 p106 p113 p120 : Prop)
    (h26836 : (¬ p101) ∨ (¬ p102))
    (h24728 : p113 ∨ (¬ p120) ∨ p106 ∨ p102) : p113 ∨ (¬ p120) ∨ p106 ∨ (¬ p101) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p113) := fun hu => hn (Or.inl hu)
  have u1 : p120 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p106) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p102) := by
    rcases h26836 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h24728 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (u2 q2)
  · exact False.elim (u4 q3)

theorem step34689 (p1385 p1389 p1393 p1405 : Prop)
    (h26932 : (¬ p1385) ∨ (¬ p1393))
    (h26332 : p1393 ∨ p1389 ∨ (¬ p1405)) : p1389 ∨ (¬ p1405) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1389) := fun hu => hn (Or.inl hu)
  have u1 : p1405 := by
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
  rcases h26332 with q0 | q1 | q2
  · exact False.elim (u3 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u1)

theorem step34692 (p1385 p1389 p1393 p1399 p1405 : Prop)
    (h26932 : (¬ p1385) ∨ (¬ p1393))
    (h26331 : p1399 ∨ p1393 ∨ (¬ p1405) ∨ p1389) : p1399 ∨ p1389 ∨ (¬ p1385) ∨ (¬ p1405) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1399) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1389) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1405 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p1393) := by
    rcases h26932 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h26331 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (u1 q3)

theorem step34693 (p224 p244 p382 p536 p657 p738 p789 p834 p858 : Prop)
    (h26887 : p657 ∨ p224)
    (h26897 : p858 ∨ p789)
    (h26334 : (¬ p657) ∨ (¬ p738) ∨ (¬ p536) ∨ (¬ p244) ∨ (¬ p834) ∨ (¬ p858) ∨ (¬ p382)) : (¬ p536) ∨ (¬ p738) ∨ (¬ p834) ∨ p224 ∨ p789 ∨ (¬ p244) ∨ (¬ p382) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p536 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p738 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p834 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p244 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h26334 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u6)

theorem step34696 (p10 p126 p186 p268 p301 p323 p419 p1055 p1061 p1076 p1077 : Prop)
    (h26857 : p301 ∨ p126)
    (h26909 : p1061 ∨ p1055)
    (h26910 : (¬ p1076) ∨ (¬ p1077))
    (h26861 : p323 ∨ p10)
    (h26337 : (¬ p1061) ∨ (¬ p419) ∨ (¬ p1076) ∨ p1077 ∨ (¬ p186) ∨ (¬ p323) ∨ (¬ p268) ∨ (¬ p301)) : p126 ∨ p1055 ∨ (¬ p1076) ∨ (¬ p419) ∨ (¬ p268) ∨ p10 ∨ (¬ p186) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p268 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : (¬ p1077) := by
    rcases h26910 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u10 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26337 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (u9 q3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step34697 (p2 p10 p126 p136 p301 p323 p424 p481 : Prop)
    (h26857 : p301 ∨ p126)
    (h26861 : p323 ∨ p10)
    (h26873 : p481 ∨ p2)
    (h26338 : (¬ p481) ∨ p424 ∨ (¬ p136) ∨ (¬ p323) ∨ (¬ p301)) : p126 ∨ p424 ∨ (¬ p136) ∨ p10 ∨ p2 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p424) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p136 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h26338 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u7)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step34699 (p10 p258 p323 p344 p662 p836 p1076 p1077 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26861 : p323 ∨ p10)
    (h26340 : (¬ p836) ∨ (¬ p1077) ∨ (¬ p258) ∨ (¬ p344) ∨ (¬ p662) ∨ (¬ p323)) : (¬ p836) ∨ (¬ p344) ∨ p1076 ∨ (¬ p258) ∨ (¬ p662) ∨ p10 := by
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
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p662 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26340 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u7)

theorem step34701 (p224 p657 p789 p1115 p1116 : Prop)
    (h26887 : p657 ∨ p224)
    (h26915 : p1116 ∨ p1115)
    (h26342 : p789 ∨ (¬ p1116) ∨ (¬ p657)) : p224 ∨ p1115 ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p224) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1115) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p789) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h26342 with q0 | q1 | q2
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)

theorem step34702 (p8 p41 p156 p224 p657 p836 p840 p922 p1096 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26887 : p657 ∨ p224)
    (h26895 : p840 ∨ p836)
    (h26343 : (¬ p1333) ∨ (¬ p156) ∨ (¬ p1096) ∨ (¬ p41) ∨ (¬ p8) ∨ (¬ p922) ∨ (¬ p657) ∨ (¬ p840)) : (¬ p1096) ∨ p1325 ∨ (¬ p922) ∨ p224 ∨ (¬ p156) ∨ (¬ p41) ∨ (¬ p8) ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p922 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h26343 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u10)

theorem step34703 (p6 p17 p101 p121 p136 p156 p185 p192 p206 p224 p256 p266 p657 p790 p1084 : Prop)
    (h26887 : p657 ∨ p224)
    (h26853 : p256 ∨ p17)
    (h26344 : (¬ p185) ∨ (¬ p192) ∨ (¬ p790) ∨ (¬ p156) ∨ (¬ p266) ∨ (¬ p256) ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p657) ∨ (¬ p1084) ∨ (¬ p206) ∨ (¬ p6) ∨ (¬ p136)) : (¬ p101) ∨ (¬ p185) ∨ (¬ p1084) ∨ (¬ p206) ∨ (¬ p6) ∨ (¬ p192) ∨ (¬ p156) ∨ (¬ p790) ∨ p224 ∨ (¬ p121) ∨ p17 ∨ (¬ p266) ∨ (¬ p136) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p136 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))))
  have u13 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u14 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u10 q1)
  rcases h26344 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u14)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u13)
  · exact False.elim (q9 u2)
  · exact False.elim (q10 u3)
  · exact False.elim (q11 u4)
  · exact False.elim (q12 u12)

theorem step34705 (p8 p16 p101 p134 p189 p224 p638 p657 p1096 p1099 : Prop)
    (h26887 : p657 ∨ p224)
    (h26912 : (¬ p1096) ∨ (¬ p1099))
    (h26346 : p1099 ∨ (¬ p16) ∨ (¬ p189) ∨ (¬ p134) ∨ (¬ p638) ∨ (¬ p8) ∨ (¬ p101) ∨ (¬ p657)) : (¬ p101) ∨ (¬ p8) ∨ p224 ∨ (¬ p134) ∨ (¬ p1096) ∨ (¬ p638) ∨ (¬ p189) ∨ (¬ p16) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p638 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : (¬ p1099) := by
    rcases h26912 with q0 | q1
    · exact False.elim (q0 u4)
    · exact q1
  rcases h26346 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u8)

theorem step34709 (p6 p101 p121 p134 p192 p422 p1084 p1206 p1256 : Prop)
    (h26922 : (¬ p121) ∨ (¬ p1206))
    (h26929 : p1256 ∨ p422)
    (h26350 : (¬ p1256) ∨ (¬ p192) ∨ (¬ p1084) ∨ (¬ p6) ∨ p1206 ∨ (¬ p134) ∨ (¬ p101)) : (¬ p101) ∨ (¬ p1084) ∨ (¬ p6) ∨ (¬ p121) ∨ p422 ∨ (¬ p134) ∨ (¬ p192) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p1206) := by
    rcases h26922 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  have u8 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h26350 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u7 q4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u0)

theorem step34711 (p8 p88 p101 p134 p142 p189 p224 p227 p422 p657 p924 : Prop)
    (h26887 : p657 ∨ p224)
    (h26840 : (¬ p134) ∨ (¬ p142))
    (h26352 : (¬ p227) ∨ (¬ p88) ∨ (¬ p422) ∨ p142 ∨ (¬ p189) ∨ (¬ p924) ∨ (¬ p8) ∨ (¬ p101) ∨ (¬ p657)) : (¬ p422) ∨ (¬ p101) ∨ (¬ p8) ∨ (¬ p227) ∨ p224 ∨ (¬ p189) ∨ (¬ p134) ∨ (¬ p88) ∨ (¬ p924) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : (¬ p142) := by
    rcases h26840 with q0 | q1
    · exact False.elim (q0 u6)
    · exact q1
  rcases h26352 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u0)
  · exact False.elim (u10 q3)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u9)

theorem step34713 (p495 p499 p595 p690 p1542 : Prop)
    (h26875 : p499 ∨ p495)
    (h26365 : (¬ p499) ∨ (¬ p690) ∨ p595 ∨ (¬ p1542)) : (¬ p1542) ∨ (¬ p690) ∨ p595 ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h26365 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u0)

theorem step34715 (p224 p344 p495 p499 p595 p616 p657 p899 p1096 : Prop)
    (h26875 : p499 ∨ p495)
    (h26883 : p616 ∨ p595)
    (h26887 : p657 ∨ p224)
    (h26367 : (¬ p344) ∨ (¬ p499) ∨ (¬ p1096) ∨ (¬ p899) ∨ (¬ p616) ∨ (¬ p657)) : p495 ∨ (¬ p344) ∨ (¬ p1096) ∨ p595 ∨ (¬ p899) ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p495) := fun hu => hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p899 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26367 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u8)

theorem step34719 (p344 p734 p897 p903 p904 p1542 : Prop)
    (h26899 : p904 ∨ p897)
    (h26378 : p344 ∨ (¬ p1542) ∨ (¬ p734) ∨ (¬ p904) ∨ (¬ p903)) : (¬ p1542) ∨ p344 ∨ (¬ p903) ∨ (¬ p734) ∨ p897 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p903 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h26378 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)

theorem step34723 (p14 p41 p45 p63 p85 p224 p229 p386 p389 p422 p495 p532 p576 p657 p1076 : Prop)
    (h26887 : p657 ∨ p224)
    (h26831 : p45 ∨ p41)
    (h26835 : p85 ∨ p63)
    (h26849 : p229 ∨ p14)
    (h26382 : (¬ p532) ∨ p1076 ∨ (¬ p576) ∨ (¬ p389) ∨ (¬ p386) ∨ (¬ p229) ∨ (¬ p495) ∨ (¬ p45) ∨ (¬ p85) ∨ (¬ p422) ∨ (¬ p657)) : (¬ p389) ∨ (¬ p422) ∨ p224 ∨ (¬ p576) ∨ p41 ∨ (¬ p532) ∨ (¬ p386) ∨ p63 ∨ p1076 ∨ p14 ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p386 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u12 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u13 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u14 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h26382 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u5)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u14)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u12)
  · exact False.elim (q8 u13)
  · exact False.elim (q9 u1)
  · exact False.elim (q10 u11)

theorem step34728 (p8 p86 p185 p224 p237 p344 p710 p897 p904 p1055 p1061 p1076 p1096 p1099 p1115 p1116 p1311 p1452 : Prop)
    (h26898 : (¬ p897) ∨ (¬ p904))
    (h26889 : p710 ∨ p8)
    (h26851 : p237 ∨ p185)
    (h26913 : p1099 ∨ p1096)
    (h26909 : p1061 ∨ p1055)
    (h26915 : p1116 ∨ p1115)
    (h26388 : (¬ p344) ∨ p904 ∨ (¬ p710) ∨ (¬ p1099) ∨ (¬ p1116) ∨ (¬ p237) ∨ (¬ p1311) ∨ p224 ∨ (¬ p86) ∨ (¬ p1061) ∨ (¬ p1452) ∨ p1076) : (¬ p897) ∨ (¬ p344) ∨ p1076 ∨ (¬ p1452) ∨ p8 ∨ p185 ∨ (¬ p1311) ∨ p1096 ∨ (¬ p86) ∨ p1055 ∨ p224 ∨ p1115 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1311 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))
  have u12 : (¬ p904) := by
    rcases h26898 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u13 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u14 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u15 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u16 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  have u17 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  rcases h26388 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (q0 u1)
  · exact False.elim (u12 q1)
  · exact False.elim (q2 u13)
  · exact False.elim (q3 u15)
  · exact False.elim (q4 u17)
  · exact False.elim (q5 u14)
  · exact False.elim (q6 u6)
  · exact False.elim (u10 q7)
  · exact False.elim (q8 u8)
  · exact False.elim (q9 u16)
  · exact False.elim (q10 u3)
  · exact False.elim (u2 q11)

theorem step34732 (p3 p14 p41 p45 p63 p85 p104 p224 p229 p422 p657 p1055 p1061 p1076 p1452 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h26830 : (¬ p41) ∨ (¬ p45))
    (h26848 : (¬ p14) ∨ (¬ p229))
    (h26835 : p85 ∨ p63)
    (h26887 : p657 ∨ p224)
    (h26392 : (¬ p3) ∨ p229 ∨ (¬ p657) ∨ p45 ∨ (¬ p422) ∨ (¬ p104) ∨ (¬ p85) ∨ (¬ p1061) ∨ (¬ p1452) ∨ p1076) : (¬ p422) ∨ (¬ p1452) ∨ (¬ p3) ∨ p1055 ∨ (¬ p41) ∨ (¬ p14) ∨ p63 ∨ p224 ∨ (¬ p104) ∨ p1076 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : (¬ p45) := by
    rcases h26830 with q0 | q1
    · exact False.elim (q0 u4)
    · exact q1
  have u12 : (¬ p229) := by
    rcases h26848 with q0 | q1
    · exact False.elim (q0 u5)
    · exact q1
  have u13 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u14 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h26392 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u2)
  · exact False.elim (u12 q1)
  · exact False.elim (q2 u14)
  · exact False.elim (u11 q3)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u13)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u1)
  · exact False.elim (u9 q9)

theorem step34734 (p3 p48 p50 p63 p84 p104 p163 p167 p185 p237 p344 p1055 p1061 p1076 p1096 p1452 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h26851 : p237 ∨ p185)
    (h26843 : p167 ∨ p163)
    (h26395 : (¬ p237) ∨ (¬ p84) ∨ p63 ∨ p1096 ∨ p3 ∨ (¬ p1061) ∨ (¬ p1452) ∨ p1076 ∨ (¬ p104) ∨ (¬ p48) ∨ (¬ p50) ∨ (¬ p167) ∨ p344) : (¬ p1452) ∨ p1076 ∨ (¬ p104) ∨ p63 ∨ p3 ∨ (¬ p84) ∨ p1096 ∨ p344 ∨ p1055 ∨ (¬ p48) ∨ (¬ p50) ∨ p185 ∨ p163 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p50 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))))
  have u13 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u14 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  have u15 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u12 q1)
  rcases h26395 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  · exact False.elim (q0 u14)
  · exact False.elim (q1 u5)
  · exact False.elim (u3 q2)
  · exact False.elim (u6 q3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u13)
  · exact False.elim (q6 u0)
  · exact False.elim (u1 q7)
  · exact False.elim (q8 u2)
  · exact False.elim (q9 u9)
  · exact False.elim (q10 u10)
  · exact False.elim (q11 u15)
  · exact False.elim (u7 q12)

theorem step34736 (p101 p102 p185 p189 p193 p258 : Prop)
    (h26837 : p102 ∨ p101)
    (h26845 : p193 ∨ p189)
    (h26397 : (¬ p258) ∨ (¬ p102) ∨ (¬ p193) ∨ (¬ p185)) : p101 ∨ (¬ p258) ∨ (¬ p185) ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p101) := fun hu => hn (Or.inl hu)
  have u1 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h26397 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)

theorem step34740 (p14 p15 p69 p108 p185 p189 p193 p225 p229 p258 p344 p382 p406 p496 p666 p790 p799 p814 p816 p1325 : Prop)
    (h26849 : p229 ∨ p14)
    (h26845 : p193 ∨ p189)
    (h26893 : p814 ∨ p790)
    (h26869 : p406 ∨ p382)
    (h26833 : p69 ∨ p15)
    (h26401 : p1325 ∨ (¬ p225) ∨ (¬ p406) ∨ (¬ p799) ∨ (¬ p816) ∨ (¬ p814) ∨ (¬ p666) ∨ p344 ∨ (¬ p496) ∨ (¬ p69) ∨ (¬ p229) ∨ (¬ p193) ∨ (¬ p108) ∨ p258 ∨ (¬ p185)) : p14 ∨ p189 ∨ p258 ∨ p1325 ∨ (¬ p185) ∨ p790 ∨ (¬ p799) ∨ (¬ p816) ∨ p382 ∨ p344 ∨ (¬ p666) ∨ (¬ p496) ∨ (¬ p108) ∨ p15 ∨ (¬ p225) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p799 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p816 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p666 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))))))
  have u15 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u16 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u17 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u18 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u19 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u13 q1)
  rcases h26401 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u14)
  · exact False.elim (q2 u18)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u17)
  · exact False.elim (q6 u10)
  · exact False.elim (u9 q7)
  · exact False.elim (q8 u11)
  · exact False.elim (q9 u19)
  · exact False.elim (q10 u15)
  · exact False.elim (q11 u16)
  · exact False.elim (q12 u12)
  · exact False.elim (u2 q13)
  · exact False.elim (q14 u4)

theorem step34743 (p8 p15 p17 p69 p185 p189 p193 p225 p256 p344 p709 p710 p1325 : Prop)
    (h26889 : p710 ∨ p8)
    (h26833 : p69 ∨ p15)
    (h26845 : p193 ∨ p189)
    (h26852 : (¬ p17) ∨ (¬ p256))
    (h26404 : (¬ p1325) ∨ (¬ p709) ∨ (¬ p710) ∨ (¬ p225) ∨ p344 ∨ (¬ p69) ∨ p256 ∨ (¬ p193) ∨ (¬ p185)) : (¬ p709) ∨ (¬ p185) ∨ p8 ∨ (¬ p1325) ∨ p344 ∨ p15 ∨ p189 ∨ (¬ p17) ∨ (¬ p225) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p709 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u11 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u12 : (¬ p256) := by
    rcases h26852 with q0 | q1
    · exact False.elim (q0 u7)
    · exact q1
  rcases h26404 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u8)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u10)
  · exact False.elim (u12 q6)
  · exact False.elim (q7 u11)
  · exact False.elim (q8 u1)

theorem step34744 (p15 p17 p69 p125 p185 p189 p193 p225 p256 p344 p362 p1055 : Prop)
    (h26845 : p193 ∨ p189)
    (h26865 : p362 ∨ p125)
    (h26833 : p69 ∨ p15)
    (h26852 : (¬ p17) ∨ (¬ p256))
    (h26405 : (¬ p225) ∨ (¬ p69) ∨ (¬ p185) ∨ (¬ p362) ∨ p344 ∨ p256 ∨ p1055 ∨ (¬ p193)) : (¬ p185) ∨ p189 ∨ p1055 ∨ p125 ∨ p15 ∨ (¬ p17) ∨ (¬ p225) ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : (¬ p256) := by
    rcases h26852 with q0 | q1
    · exact False.elim (q0 u5)
    · exact q1
  rcases h26405 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u9)
  · exact False.elim (u7 q4)
  · exact False.elim (u11 q5)
  · exact False.elim (u2 q6)
  · exact False.elim (q7 u8)

theorem step34745 (p15 p69 p125 p189 p193 p303 p362 p387 p431 p496 p576 p790 p1713 : Prop)
    (h26845 : p193 ∨ p189)
    (h26865 : p362 ∨ p125)
    (h26867 : p387 ∨ p303)
    (h26833 : p69 ∨ p15)
    (h26424 : (¬ p193) ∨ (¬ p1713) ∨ p790 ∨ (¬ p576) ∨ (¬ p496) ∨ (¬ p387) ∨ (¬ p362) ∨ (¬ p431) ∨ (¬ p69)) : (¬ p1713) ∨ (¬ p431) ∨ p189 ∨ p125 ∨ p790 ∨ (¬ p576) ∨ (¬ p496) ∨ p303 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1713 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u12 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h26424 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u0)
  · exact False.elim (u4 q2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u12)

theorem step34747 (p63 p85 p125 p134 p189 p303 p362 p387 p496 p576 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26867 : p387 ∨ p303)
    (h26835 : p85 ∨ p63)
    (h26865 : p362 ∨ p125)
    (h26426 : (¬ p85) ∨ (¬ p134) ∨ (¬ p576) ∨ (¬ p1333) ∨ (¬ p189) ∨ (¬ p496) ∨ (¬ p387) ∨ (¬ p362)) : p1325 ∨ (¬ p576) ∨ p303 ∨ (¬ p134) ∨ p63 ∨ (¬ p496) ∨ p125 ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1325) := fun hu => hn (Or.inl hu)
  have u1 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h26426 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u11)

theorem step34748 (p15 p69 p125 p224 p234 p303 p362 p387 p496 p657 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26867 : p387 ∨ p303)
    (h26886 : (¬ p224) ∨ (¬ p657))
    (h26865 : p362 ∨ p125)
    (h26833 : p69 ∨ p15)
    (h26428 : p657 ∨ (¬ p1187) ∨ (¬ p496) ∨ (¬ p387) ∨ (¬ p362) ∨ (¬ p69)) : p234 ∨ p303 ∨ (¬ p224) ∨ (¬ p496) ∨ p125 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : (¬ p657) := by
    rcases h26886 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u9 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26428 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)

theorem step34750 (p15 p63 p69 p224 p234 p419 p477 p595 p616 p657 p680 p996 p1187 : Prop)
    (h26886 : (¬ p224) ∨ (¬ p657))
    (h26833 : p69 ∨ p15)
    (h26921 : p1187 ∨ p234)
    (h26905 : p996 ∨ p419)
    (h26883 : p616 ∨ p595)
    (h26430 : (¬ p996) ∨ p657 ∨ (¬ p680) ∨ (¬ p477) ∨ (¬ p1187) ∨ (¬ p616) ∨ (¬ p69) ∨ (¬ p63)) : (¬ p477) ∨ (¬ p224) ∨ p15 ∨ (¬ p63) ∨ p234 ∨ p419 ∨ (¬ p680) ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p477 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p234) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p657) := by
    rcases h26886 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  have u9 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u12 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h26430 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u11)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u12)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u3)

theorem step34751 (p14 p15 p63 p69 p101 p229 p633 p636 : Prop)
    (h26885 : p636 ∨ p633)
    (h26849 : p229 ∨ p14)
    (h26833 : p69 ∨ p15)
    (h26431 : p101 ∨ (¬ p636) ∨ (¬ p229) ∨ (¬ p69) ∨ (¬ p63)) : p633 ∨ p101 ∨ (¬ p63) ∨ p14 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p101) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h26431 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u2)

theorem step34753 (p15 p63 p69 p576 : Prop)
    (h26833 : p69 ∨ p15)
    (h26433 : p576 ∨ (¬ p69) ∨ (¬ p63)) : p576 ∨ p15 ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p576) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h26433 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)

theorem step34754 (p14 p15 p18 p63 p69 p229 p234 p1187 : Prop)
    (h26849 : p229 ∨ p14)
    (h26921 : p1187 ∨ p234)
    (h26833 : p69 ∨ p15)
    (h26434 : p18 ∨ (¬ p1187) ∨ (¬ p229) ∨ (¬ p69) ∨ (¬ p63)) : p14 ∨ p18 ∨ p234 ∨ p15 ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p18) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p234) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h26434 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u4)

theorem step34755 (p6 p10 p67 p101 p102 p137 p258 p288 p303 p387 p640 p1095 : Prop)
    (h26867 : p387 ∨ p303)
    (h26837 : p102 ∨ p101)
    (h26855 : p288 ∨ p258)
    (h26435 : (¬ p10) ∨ (¬ p387) ∨ (¬ p288) ∨ (¬ p1095) ∨ (¬ p640) ∨ (¬ p102) ∨ (¬ p6) ∨ (¬ p137) ∨ (¬ p67)) : p303 ∨ (¬ p10) ∨ (¬ p1095) ∨ p101 ∨ (¬ p137) ∨ p258 ∨ (¬ p640) ∨ (¬ p6) ∨ (¬ p67) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p137 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p640 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26435 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u8)

theorem step34756 (p126 p258 p288 p303 p310 p387 p576 p581 p1055 p1061 : Prop)
    (h26867 : p387 ∨ p303)
    (h26878 : (¬ p576) ∨ (¬ p581))
    (h26855 : p288 ∨ p258)
    (h26909 : p1061 ∨ p1055)
    (h26436 : p126 ∨ (¬ p387) ∨ (¬ p1061) ∨ (¬ p310) ∨ (¬ p288) ∨ p581) : p126 ∨ p303 ∨ (¬ p576) ∨ p258 ∨ p1055 ∨ (¬ p310) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : (¬ p581) := by
    rcases h26878 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u8 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h26436 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u8)
  · exact False.elim (u7 q5)

theorem step34759 (p8 p17 p138 p163 p167 p185 p186 p344 p346 : Prop)
    (h26843 : p167 ∨ p163)
    (h26863 : p346 ∨ p344)
    (h26451 : (¬ p17) ∨ (¬ p167) ∨ p185 ∨ (¬ p138) ∨ (¬ p186) ∨ (¬ p346) ∨ (¬ p8)) : p185 ∨ (¬ p186) ∨ p163 ∨ (¬ p138) ∨ (¬ p17) ∨ (¬ p8) ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p185) := fun hu => hn (Or.inl hu)
  have u1 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h26451 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u7)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u5)

theorem step34763 (p15 p17 p63 p84 p85 p126 p256 p303 p387 p1229 p1232 p1295 : Prop)
    (h26867 : p387 ∨ p303)
    (h26835 : p85 ∨ p63)
    (h26853 : p256 ∨ p17)
    (h26927 : p1232 ∨ p1229)
    (h26456 : (¬ p15) ∨ (¬ p1295) ∨ (¬ p387) ∨ (¬ p126) ∨ (¬ p1232) ∨ (¬ p85) ∨ (¬ p256) ∨ (¬ p84)) : (¬ p15) ∨ (¬ p1295) ∨ (¬ p84) ∨ (¬ p126) ∨ p303 ∨ p63 ∨ p17 ∨ p1229 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1295 := by
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
  have u4 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h26456 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u2)

theorem step34768 (p18 p134 p1385 p1393 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h26461 : (¬ p18) ∨ p134 ∨ (¬ p1393)) : (¬ p18) ∨ p1385 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1385) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h26461 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)

theorem step34774 (p8 p227 p258 p268 p344 p346 : Prop)
    (h26863 : p346 ∨ p344)
    (h26468 : (¬ p346) ∨ (¬ p8) ∨ (¬ p227) ∨ (¬ p268) ∨ (¬ p258)) : (¬ p258) ∨ p344 ∨ (¬ p227) ∨ (¬ p8) ∨ (¬ p268) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p268 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h26468 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u0)

theorem step34776 (p8 p160 p309 p532 p668 p710 p1076 : Prop)
    (h26889 : p710 ∨ p8)
    (h26470 : p1076 ∨ (¬ p710) ∨ (¬ p309) ∨ (¬ p160) ∨ (¬ p532) ∨ (¬ p668)) : (¬ p160) ∨ p1076 ∨ p8 ∨ (¬ p532) ∨ (¬ p309) ∨ (¬ p668) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h26470 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)

theorem step34777 (p11 p17 p258 p288 p303 p387 p496 p728 p980 p1074 p1081 p1096 p1099 p1330 p1443 : Prop)
    (h26867 : p387 ∨ p303)
    (h26913 : p1099 ∨ p1096)
    (h26855 : p288 ∨ p258)
    (h26935 : p1443 ∨ p11)
    (h26471 : p17 ∨ (¬ p496) ∨ (¬ p1099) ∨ (¬ p1443) ∨ (¬ p728) ∨ (¬ p288) ∨ (¬ p1074) ∨ (¬ p980) ∨ (¬ p387) ∨ (¬ p1330) ∨ (¬ p1081)) : p303 ∨ p17 ∨ (¬ p728) ∨ (¬ p496) ∨ p1096 ∨ p258 ∨ p11 ∨ (¬ p980) ∨ (¬ p1074) ∨ (¬ p1330) ∨ (¬ p1081) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u12 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u13 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u14 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h26471 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u12)
  · exact False.elim (q3 u14)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u13)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u11)
  · exact False.elim (q9 u9)
  · exact False.elim (q10 u10)

theorem step34779 (p12 p124 p125 p1036 p1074 p1076 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26906 : (¬ p12) ∨ (¬ p1036))
    (h26475 : p1036 ∨ (¬ p1074) ∨ (¬ p1099) ∨ (¬ p1076) ∨ (¬ p124) ∨ (¬ p125)) : (¬ p125) ∨ (¬ p1076) ∨ (¬ p124) ∨ p1096 ∨ (¬ p1074) ∨ (¬ p12) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : (¬ p1036) := by
    rcases h26906 with q0 | q1
    · exact False.elim (q0 u5)
    · exact q1
  rcases h26475 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u0)

theorem step34786 (p10 p15 p16 p17 p39 p63 p69 p88 p124 p125 p256 p258 p288 p323 p419 p458 p790 p814 p816 p1080 p1096 p1335 p1452 : Prop)
    (h26860 : (¬ p10) ∨ (¬ p323))
    (h26855 : p288 ∨ p258)
    (h26893 : p814 ∨ p790)
    (h26852 : (¬ p17) ∨ (¬ p256))
    (h26833 : p69 ∨ p15)
    (h26483 : (¬ p419) ∨ (¬ p816) ∨ (¬ p814) ∨ (¬ p458) ∨ (¬ p39) ∨ (¬ p16) ∨ (¬ p88) ∨ (¬ p63) ∨ p323 ∨ (¬ p69) ∨ (¬ p1096) ∨ p256 ∨ (¬ p1452) ∨ (¬ p1335) ∨ (¬ p288) ∨ (¬ p1080) ∨ (¬ p124) ∨ (¬ p125)) : (¬ p88) ∨ (¬ p10) ∨ (¬ p419) ∨ (¬ p125) ∨ (¬ p458) ∨ (¬ p16) ∨ (¬ p39) ∨ p258 ∨ (¬ p63) ∨ p790 ∨ (¬ p1096) ∨ (¬ p17) ∨ (¬ p816) ∨ p15 ∨ (¬ p1335) ∨ (¬ p1452) ∨ (¬ p124) ∨ (¬ p1080) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p458 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p816 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))
  have u15 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))
  have u16 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))
  have u17 : p1080 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))))))))
  have u18 : (¬ p323) := by
    rcases h26860 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  have u19 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u20 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  have u21 : (¬ p256) := by
    rcases h26852 with q0 | q1
    · exact False.elim (q0 u11)
    · exact q1
  have u22 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u13 q1)
  rcases h26483 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14 | q15 | q16 | q17
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u12)
  · exact False.elim (q2 u20)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u8)
  · exact False.elim (u18 q8)
  · exact False.elim (q9 u22)
  · exact False.elim (q10 u10)
  · exact False.elim (u21 q11)
  · exact False.elim (q12 u15)
  · exact False.elim (q13 u14)
  · exact False.elim (q14 u19)
  · exact False.elim (q15 u17)
  · exact False.elim (q16 u16)
  · exact False.elim (q17 u3)

theorem step34788 (p15 p63 p69 p85 p419 p537 p836 p996 p1096 p1192 p1332 p1562 : Prop)
    (h26834 : (¬ p63) ∨ (¬ p85))
    (h26905 : p996 ∨ p419)
    (h26833 : p69 ∨ p15)
    (h26486 : p85 ∨ (¬ p1562) ∨ (¬ p537) ∨ (¬ p836) ∨ (¬ p1192) ∨ (¬ p996) ∨ (¬ p1332) ∨ (¬ p1096) ∨ (¬ p69)) : (¬ p537) ∨ (¬ p1562) ∨ (¬ p63) ∨ (¬ p836) ∨ (¬ p1192) ∨ p419 ∨ (¬ p1332) ∨ (¬ p1096) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1562 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1332 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p85) := by
    rcases h26834 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u10 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u11 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h26486 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u11)

theorem step34790 (p41 p63 p85 p225 p1096 : Prop)
    (h26835 : p85 ∨ p63)
    (h26488 : p41 ∨ (¬ p225) ∨ (¬ p85) ∨ (¬ p1096)) : (¬ p1096) ∨ p63 ∨ (¬ p225) ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p63) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h26488 with q0 | q1 | q2 | q3
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step34792 (p2 p41 p87 p189 p419 p431 p481 p996 p1015 : Prop)
    (h26905 : p996 ∨ p419)
    (h26873 : p481 ∨ p2)
    (h26491 : (¬ p189) ∨ (¬ p481) ∨ (¬ p431) ∨ (¬ p1015) ∨ (¬ p41) ∨ (¬ p87) ∨ (¬ p996)) : (¬ p431) ∨ (¬ p1015) ∨ p419 ∨ p2 ∨ (¬ p41) ∨ (¬ p87) ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h26491 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u7)

theorem step34793 (p15 p69 p163 p1096 : Prop)
    (h26833 : p69 ∨ p15)
    (h26492 : p163 ∨ (¬ p1096) ∨ (¬ p69)) : (¬ p1096) ∨ p163 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h26492 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)

theorem step34795 (p10 p419 p420 p435 p996 p1542 : Prop)
    (h26905 : p996 ∨ p419)
    (h26494 : p420 ∨ (¬ p10) ∨ (¬ p435) ∨ (¬ p1542) ∨ (¬ p996)) : (¬ p1542) ∨ (¬ p10) ∨ (¬ p435) ∨ p420 ∨ p419 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h26494 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)

theorem step34797 (p2 p63 p85 p163 p189 p419 p431 p435 p481 p595 p996 p1096 : Prop)
    (h26873 : p481 ∨ p2)
    (h26905 : p996 ∨ p419)
    (h26835 : p85 ∨ p63)
    (h26497 : (¬ p435) ∨ (¬ p431) ∨ (¬ p163) ∨ p189 ∨ (¬ p481) ∨ p595 ∨ (¬ p996) ∨ (¬ p85) ∨ (¬ p1096)) : (¬ p1096) ∨ p595 ∨ (¬ p435) ∨ (¬ p163) ∨ p2 ∨ (¬ p431) ∨ p419 ∨ p189 ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p595) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h26497 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (u7 q3)
  · exact False.elim (q4 u9)
  · exact False.elim (u1 q5)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u11)
  · exact False.elim (q8 u0)

theorem step34800 (p15 p63 p69 p85 p134 p142 p189 p419 p424 p495 p499 p996 p1080 p1095 p1096 p1140 p1366 : Prop)
    (h26833 : p69 ∨ p15)
    (h26841 : p142 ∨ p134)
    (h26905 : p996 ∨ p419)
    (h26835 : p85 ∨ p63)
    (h26875 : p499 ∨ p495)
    (h26500 : (¬ p424) ∨ (¬ p69) ∨ (¬ p1140) ∨ (¬ p142) ∨ p189 ∨ p1095 ∨ (¬ p85) ∨ (¬ p499) ∨ (¬ p1096) ∨ (¬ p1366) ∨ (¬ p996) ∨ (¬ p1080)) : (¬ p1366) ∨ p15 ∨ (¬ p424) ∨ p134 ∨ p419 ∨ p189 ∨ p63 ∨ p495 ∨ (¬ p1140) ∨ p1095 ∨ (¬ p1096) ∨ (¬ p1080) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p1095) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p1080 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))
  have u12 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u13 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u14 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u15 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u16 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h26500 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u12)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u13)
  · exact False.elim (u5 q4)
  · exact False.elim (u9 q5)
  · exact False.elim (q6 u15)
  · exact False.elim (q7 u16)
  · exact False.elim (q8 u10)
  · exact False.elim (q9 u0)
  · exact False.elim (q10 u14)
  · exact False.elim (q11 u11)

theorem step34804 (p10 p15 p63 p69 p85 p103 p124 p160 p189 p304 p323 p419 p424 p495 p499 p582 p796 p980 p996 p1076 p1077 p1095 p1096 p1366 : Prop)
    (h26860 : (¬ p10) ∨ (¬ p323))
    (h26833 : p69 ∨ p15)
    (h26859 : p304 ∨ p124)
    (h26910 : (¬ p1076) ∨ (¬ p1077))
    (h26875 : p499 ∨ p495)
    (h26891 : p796 ∨ p424)
    (h26905 : p996 ∨ p419)
    (h26835 : p85 ∨ p63)
    (h26512 : (¬ p1096) ∨ (¬ p1366) ∨ p160 ∨ p980 ∨ (¬ p103) ∨ p323 ∨ (¬ p69) ∨ (¬ p304) ∨ p1095 ∨ p1077 ∨ (¬ p499) ∨ (¬ p796) ∨ p189 ∨ (¬ p996) ∨ (¬ p582) ∨ (¬ p85)) : p160 ∨ p980 ∨ (¬ p1096) ∨ (¬ p1366) ∨ (¬ p103) ∨ (¬ p10) ∨ p15 ∨ p124 ∨ p1095 ∨ (¬ p1076) ∨ p495 ∨ p424 ∨ p189 ∨ p419 ∨ (¬ p582) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p160) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p1095) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : (¬ p424) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))
  have u15 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))))))
  have u16 : (¬ p323) := by
    rcases h26860 with q0 | q1
    · exact False.elim (q0 u5)
    · exact q1
  have u17 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u18 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u19 : (¬ p1077) := by
    rcases h26910 with q0 | q1
    · exact False.elim (q0 u9)
    · exact q1
  have u20 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u10 q1)
  have u21 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  have u22 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u13 q1)
  have u23 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u15 q1)
  rcases h26512 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14 | q15
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (u16 q5)
  · exact False.elim (q6 u17)
  · exact False.elim (q7 u18)
  · exact False.elim (u8 q8)
  · exact False.elim (u19 q9)
  · exact False.elim (q10 u20)
  · exact False.elim (q11 u21)
  · exact False.elim (u12 q12)
  · exact False.elim (q13 u22)
  · exact False.elim (q14 u14)
  · exact False.elim (q15 u23)

theorem step34809 (p303 p419 p996 p1325 p1333 p1465 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26904 : (¬ p419) ∨ (¬ p996))
    (h26517 : p303 ∨ (¬ p1465) ∨ (¬ p1333) ∨ p996) : p303 ∨ p1325 ∨ (¬ p419) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : (¬ p996) := by
    rcases h26904 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h26517 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (u5 q3)

theorem step34815 (p633 p636 p1055 p1061 p1076 : Prop)
    (h26885 : p636 ∨ p633)
    (h26909 : p1061 ∨ p1055)
    (h26526 : (¬ p1061) ∨ (¬ p636) ∨ (¬ p1076)) : p633 ∨ p1055 ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h26526 with q0 | q1 | q2
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)

theorem step34816 (p3 p134 p163 p167 p224 p226 p633 p657 p1076 : Prop)
    (h26846 : (¬ p3) ∨ (¬ p226))
    (h26843 : p167 ∨ p163)
    (h26886 : (¬ p224) ∨ (¬ p657))
    (h26527 : p226 ∨ (¬ p167) ∨ p657 ∨ (¬ p134) ∨ p633 ∨ (¬ p1076)) : (¬ p3) ∨ p633 ∨ (¬ p1076) ∨ (¬ p134) ∨ p163 ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p633) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p226) := by
    rcases h26846 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u7 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u8 : (¬ p657) := by
    rcases h26886 with q0 | q1
    · exact False.elim (q0 u5)
    · exact q1
  rcases h26527 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u7)
  · exact False.elim (u8 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (u1 q4)
  · exact False.elim (q5 u2)

theorem step34817 (p90 p185 p237 p258 p578 p633 p636 : Prop)
    (h26885 : p636 ∨ p633)
    (h26586 : p90)
    (h26851 : p237 ∨ p185)
    (h26528 : p258 ∨ (¬ p237) ∨ (¬ p90) ∨ (¬ p578) ∨ (¬ p636)) : p633 ∨ (¬ p578) ∨ p258 ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : p578 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p90 := by
    exact h26586
  have u6 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h26528 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)

theorem step34818 (p23 p90 p101 p102 p185 p224 p237 p258 p576 p634 p657 p1076 : Prop)
    (h26586 : p90)
    (h26837 : p102 ∨ p101)
    (h26851 : p237 ∨ p185)
    (h26886 : (¬ p224) ∨ (¬ p657))
    (h26529 : (¬ p576) ∨ (¬ p258) ∨ (¬ p237) ∨ (¬ p90) ∨ (¬ p23) ∨ (¬ p102) ∨ p657 ∨ (¬ p634) ∨ (¬ p1076)) : (¬ p258) ∨ (¬ p576) ∨ (¬ p1076) ∨ p101 ∨ (¬ p23) ∨ p185 ∨ (¬ p634) ∨ (¬ p224) := by
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
  have u2 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p23 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p634 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p90 := by
    exact h26586
  have u9 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u11 : (¬ p657) := by
    rcases h26886 with q0 | q1
    · exact False.elim (q0 u7)
    · exact q1
  rcases h26529 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u9)
  · exact False.elim (u11 q6)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u2)

theorem step34819 (p2 p12 p14 p23 p63 p101 p102 p124 p185 p209 p224 p229 p237 p258 p304 p344 p346 p576 p581 p634 p657 p1036 p1076 p1077 p1096 p1188 : Prop)
    (h26849 : p229 ∨ p14)
    (h26886 : (¬ p224) ∨ (¬ p657))
    (h26907 : p1036 ∨ p12)
    (h26862 : (¬ p344) ∨ (¬ p346))
    (h26859 : p304 ∨ p124)
    (h26910 : (¬ p1076) ∨ (¬ p1077))
    (h26837 : p102 ∨ p101)
    (h26879 : p581 ∨ p576)
    (h26851 : p237 ∨ p185)
    (h26530 : p346 ∨ (¬ p1188) ∨ (¬ p2) ∨ (¬ p1036) ∨ (¬ p209) ∨ (¬ p304) ∨ (¬ p1096) ∨ (¬ p229) ∨ (¬ p102) ∨ p657 ∨ (¬ p23) ∨ (¬ p581) ∨ (¬ p258) ∨ (¬ p237) ∨ (¬ p63) ∨ (¬ p634) ∨ p1077) : (¬ p1188) ∨ p14 ∨ (¬ p224) ∨ p12 ∨ (¬ p209) ∨ (¬ p344) ∨ p124 ∨ (¬ p1076) ∨ (¬ p2) ∨ (¬ p1096) ∨ p101 ∨ p576 ∨ (¬ p258) ∨ p185 ∨ (¬ p63) ∨ (¬ p634) ∨ (¬ p23) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p14) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))
  have u15 : p634 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))
  have u16 : p23 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))))))))
  have u17 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u18 : (¬ p657) := by
    rcases h26886 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u19 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u20 : (¬ p346) := by
    rcases h26862 with q0 | q1
    · exact False.elim (q0 u5)
    · exact q1
  have u21 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u22 : (¬ p1077) := by
    rcases h26910 with q0 | q1
    · exact False.elim (q0 u7)
    · exact q1
  have u23 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u10 q1)
  have u24 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  have u25 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u13 q1)
  rcases h26530 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14 | q15 | q16
  · exact False.elim (u20 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u19)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u21)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u17)
  · exact False.elim (q8 u23)
  · exact False.elim (u18 q9)
  · exact False.elim (q10 u16)
  · exact False.elim (q11 u24)
  · exact False.elim (q12 u12)
  · exact False.elim (q13 u25)
  · exact False.elim (q14 u14)
  · exact False.elim (q15 u15)
  · exact False.elim (u22 q16)

theorem step34821 (p1 p2 p15 p69 p101 p102 p124 p234 p481 : Prop)
    (h26832 : (¬ p15) ∨ (¬ p69))
    (h26836 : (¬ p101) ∨ (¬ p102))
    (h26873 : p481 ∨ p2)
    (h26533 : p234 ∨ (¬ p481) ∨ (¬ p1) ∨ p69 ∨ (¬ p124) ∨ p102) : p234 ∨ (¬ p15) ∨ (¬ p124) ∨ (¬ p101) ∨ (¬ p1) ∨ p2 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p69) := by
    rcases h26832 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  have u7 : (¬ p102) := by
    rcases h26836 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  have u8 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26533 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u4)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (u7 q5)

theorem step34828 (p63 p85 p89 : Prop)
    (h26834 : (¬ p63) ∨ (¬ p85))
    (h26545 : p89 ∨ p85) : p89 ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p89) := fun hu => hn (Or.inl hu)
  have u1 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p85) := by
    rcases h26834 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h26545 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step34835 (p17 p90 p124 p576 p581 p633 p636 : Prop)
    (h26885 : p636 ∨ p633)
    (h26878 : (¬ p576) ∨ (¬ p581))
    (h26586 : p90)
    (h26548 : p581 ∨ p17 ∨ (¬ p90) ∨ (¬ p636) ∨ (¬ p124)) : p633 ∨ (¬ p576) ∨ p17 ∨ (¬ p124) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : (¬ p581) := by
    rcases h26878 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  have u6 : p90 := by
    exact h26586
  rcases h26548 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u5 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)

theorem step34836 (p8 p41 p45 p63 p85 p89 p90 p124 p189 p193 p224 p633 p636 p710 : Prop)
    (h26885 : p636 ∨ p633)
    (h26845 : p193 ∨ p189)
    (h26889 : p710 ∨ p8)
    (h26586 : p90)
    (h26831 : p45 ∨ p41)
    (h26834 : (¬ p63) ∨ (¬ p85))
    (h26549 : (¬ p45) ∨ (¬ p224) ∨ (¬ p710) ∨ (¬ p193) ∨ (¬ p90) ∨ p85 ∨ (¬ p89) ∨ (¬ p636) ∨ (¬ p124)) : p633 ∨ p189 ∨ (¬ p224) ∨ p8 ∨ (¬ p124) ∨ (¬ p89) ∨ p41 ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p90 := by
    exact h26586
  have u12 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u13 : (¬ p85) := by
    rcases h26834 with q0 | q1
    · exact False.elim (q0 u7)
    · exact q1
  rcases h26549 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u12)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u11)
  · exact False.elim (u13 q5)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u4)

theorem step34840 (p10 p125 p134 p213 p323 p362 p424 p796 : Prop)
    (h26860 : (¬ p10) ∨ (¬ p323))
    (h26891 : p796 ∨ p424)
    (h26865 : p362 ∨ p125)
    (h26554 : (¬ p796) ∨ p323 ∨ p134 ∨ (¬ p362) ∨ (¬ p213)) : (¬ p10) ∨ p424 ∨ p125 ∨ p134 ∨ (¬ p213) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p424) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p213 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p323) := by
    rcases h26860 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u6 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h26554 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (u5 q1)
  · exact False.elim (u3 q2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u4)

theorem step34843 (p10 p125 p323 p362 p1140 p1159 p1209 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26860 : (¬ p10) ∨ (¬ p323))
    (h26865 : p362 ∨ p125)
    (h26564 : p323 ∨ (¬ p362) ∨ (¬ p1209) ∨ (¬ p1159)) : p1140 ∨ (¬ p10) ∨ (¬ p1209) ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : (¬ p323) := by
    rcases h26860 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  have u6 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h26564 with q0 | q1 | q2 | q3
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step34847 (p6 p10 p125 p134 p142 p206 p323 : Prop)
    (h26841 : p142 ∨ p134)
    (h26861 : p323 ∨ p10)
    (h26568 : (¬ p142) ∨ (¬ p6) ∨ (¬ p206) ∨ (¬ p323) ∨ (¬ p125)) : (¬ p125) ∨ p134 ∨ (¬ p6) ∨ (¬ p206) ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p134) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h26568 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u0)

theorem step34848 (p419 p996 p1000 : Prop)
    (h26904 : (¬ p419) ∨ (¬ p996))
    (h26672 : p1000 ∨ p996) : p1000 ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1000) := fun hu => hn (Or.inl hu)
  have u1 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p996) := by
    rcases h26904 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h26672 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step34852 (p8 p419 p996 p1055 : Prop)
    (h26905 : p996 ∨ p419)
    (h26576 : (¬ p8) ∨ (¬ p1055) ∨ (¬ p996)) : (¬ p1055) ∨ (¬ p8) ∨ p419 := by
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
  have u2 : (¬ p419) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h26576 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)

theorem step34853 (p8 p224 p419 p657 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h26886 : (¬ p224) ∨ (¬ p657))
    (h26577 : p657 ∨ p8 ∨ (¬ p996)) : p419 ∨ p8 ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p8) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : (¬ p657) := by
    rcases h26886 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h26577 with q0 | q1 | q2
  · exact False.elim (u4 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)

theorem step34854 (p8 p10 p124 p209 p323 p344 p710 : Prop)
    (h26861 : p323 ∨ p10)
    (h26889 : p710 ∨ p8)
    (h26578 : (¬ p344) ∨ p124 ∨ (¬ p209) ∨ (¬ p323) ∨ (¬ p710)) : p124 ∨ (¬ p344) ∨ p10 ∨ p8 ∨ (¬ p209) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h26578 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)

theorem step34855 (p8 p10 p124 p209 p225 p323 p544 p710 : Prop)
    (h26877 : p544 ∨ p225)
    (h26889 : p710 ∨ p8)
    (h26861 : p323 ∨ p10)
    (h26579 : p124 ∨ (¬ p209) ∨ (¬ p323) ∨ (¬ p544) ∨ (¬ p710)) : p124 ∨ p225 ∨ p8 ∨ p10 ∨ (¬ p209) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h26579 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)

theorem step34858 (p134 p163 p167 p189 p382 p406 p940 p985 p1325 p1333 : Prop)
    (h26869 : p406 ∨ p382)
    (h26843 : p167 ∨ p163)
    (h26931 : p1333 ∨ p1325)
    (h26582 : (¬ p189) ∨ (¬ p134) ∨ (¬ p167) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1333) ∨ (¬ p406)) : (¬ p940) ∨ p382 ∨ (¬ p189) ∨ (¬ p134) ∨ (¬ p985) ∨ p163 ∨ p1325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u9 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h26582 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u7)

theorem step34859 (p90 p126 p185 p237 p258 p301 p515 p574 p578 p790 p814 : Prop)
    (h26857 : p301 ∨ p126)
    (h26586 : p90)
    (h26893 : p814 ∨ p790)
    (h26851 : p237 ∨ p185)
    (h26583 : p258 ∨ (¬ p90) ∨ (¬ p574) ∨ (¬ p237) ∨ (¬ p814) ∨ (¬ p578) ∨ (¬ p301) ∨ (¬ p515)) : p126 ∨ (¬ p578) ∨ (¬ p574) ∨ p790 ∨ p258 ∨ p185 ∨ (¬ p515) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p578 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p574 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p515 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p90 := by
    exact h26586
  have u9 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26583 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u6)

theorem step34860 (p101 p102 p124 p189 p193 p258 p516 p790 p814 : Prop)
    (h26845 : p193 ∨ p189)
    (h26837 : p102 ∨ p101)
    (h26893 : p814 ∨ p790)
    (h26584 : (¬ p258) ∨ (¬ p814) ∨ (¬ p193) ∨ (¬ p516) ∨ (¬ p102) ∨ (¬ p124)) : (¬ p516) ∨ (¬ p258) ∨ p189 ∨ (¬ p124) ∨ p101 ∨ p790 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p516 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u8 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26584 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u3)

theorem step34861 (p101 p102 p124 p126 p189 p193 p301 p382 p406 p515 p516 p578 p790 p985 p1325 p1333 p1584 : Prop)
    (h26845 : p193 ∨ p189)
    (h26857 : p301 ∨ p126)
    (h26931 : p1333 ∨ p1325)
    (h26869 : p406 ∨ p382)
    (h26837 : p102 ∨ p101)
    (h26585 : p790 ∨ (¬ p193) ∨ (¬ p516) ∨ (¬ p578) ∨ (¬ p301) ∨ (¬ p515) ∨ (¬ p1584) ∨ (¬ p985) ∨ (¬ p1333) ∨ (¬ p406) ∨ (¬ p102) ∨ (¬ p124)) : (¬ p1584) ∨ (¬ p516) ∨ p189 ∨ p790 ∨ p126 ∨ (¬ p515) ∨ (¬ p578) ∨ (¬ p985) ∨ p1325 ∨ p382 ∨ p101 ∨ (¬ p124) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p516 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p126) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p515 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p578 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))
  have u12 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u13 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u14 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u15 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  have u16 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u10 q1)
  rcases h26585 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u12)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u13)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u14)
  · exact False.elim (q9 u15)
  · exact False.elim (q10 u16)
  · exact False.elim (q11 u11)

theorem step34862 (p790 p814 p822 : Prop)
    (h26892 : (¬ p790) ∨ (¬ p814))
    (h26592 : p822 ∨ p814) : p822 ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p822) := fun hu => hn (Or.inl hu)
  have u1 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p814) := by
    rcases h26892 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h26592 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step34866 (p382 p406 p822 p1325 p1333 p1489 : Prop)
    (h26869 : p406 ∨ p382)
    (h26931 : p1333 ∨ p1325)
    (h26593 : (¬ p1489) ∨ (¬ p406) ∨ (¬ p1333) ∨ (¬ p822)) : p382 ∨ p1325 ∨ (¬ p1489) ∨ (¬ p822) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p822 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h26593 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)

theorem step34868 (p63 p125 p268 p303 p362 p387 p514 p515 p576 p581 p1325 p1333 : Prop)
    (h26879 : p581 ∨ p576)
    (h26865 : p362 ∨ p125)
    (h26867 : p387 ∨ p303)
    (h26931 : p1333 ∨ p1325)
    (h26595 : (¬ p362) ∨ (¬ p63) ∨ (¬ p581) ∨ (¬ p387) ∨ (¬ p514) ∨ (¬ p515) ∨ (¬ p268) ∨ (¬ p1333)) : (¬ p514) ∨ (¬ p515) ∨ p576 ∨ (¬ p63) ∨ p125 ∨ p303 ∨ (¬ p268) ∨ p1325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p514 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p515 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p268 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u11 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h26595 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u11)

theorem step34869 (p10 p47 p63 p101 p102 p258 p539 p595 p633 p726 p985 p1273 p1508 : Prop)
    (h26837 : p102 ∨ p101)
    (h26596 : (¬ p102) ∨ (¬ p539) ∨ (¬ p47) ∨ (¬ p726) ∨ (¬ p985) ∨ (¬ p1273) ∨ (¬ p1508) ∨ (¬ p10) ∨ (¬ p258) ∨ p633 ∨ (¬ p595) ∨ (¬ p63)) : (¬ p10) ∨ p633 ∨ (¬ p47) ∨ (¬ p539) ∨ (¬ p985) ∨ p101 ∨ (¬ p726) ∨ (¬ p1273) ∨ (¬ p1508) ∨ (¬ p258) ∨ (¬ p595) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p633) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p539 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))
  have u12 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26596 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (q0 u12)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u0)
  · exact False.elim (q8 u9)
  · exact False.elim (u1 q9)
  · exact False.elim (q10 u10)
  · exact False.elim (q11 u11)

theorem step34871 (p10 p47 p134 p142 p163 p224 p234 p323 p657 p789 p858 : Prop)
    (h26860 : (¬ p10) ∨ (¬ p323))
    (h26841 : p142 ∨ p134)
    (h26887 : p657 ∨ p224)
    (h26897 : p858 ∨ p789)
    (h26598 : p234 ∨ (¬ p142) ∨ p134 ∨ (¬ p163) ∨ (¬ p47) ∨ (¬ p657) ∨ p323 ∨ (¬ p858)) : (¬ p10) ∨ p234 ∨ p134 ∨ (¬ p163) ∨ p224 ∨ (¬ p47) ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p234) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p323) := by
    rcases h26860 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u8 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h26598 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u8)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u9)
  · exact False.elim (u7 q6)
  · exact False.elim (q7 u10)

theorem step34872 (p4 p8 p12 p41 p63 p124 p134 p142 p258 p345 p424 p542 p656 p710 p1036 : Prop)
    (h26841 : p142 ∨ p134)
    (h26889 : p710 ∨ p8)
    (h26907 : p1036 ∨ p12)
    (h26611 : (¬ p142) ∨ (¬ p656) ∨ (¬ p710) ∨ (¬ p4) ∨ (¬ p345) ∨ (¬ p124) ∨ (¬ p1036) ∨ (¬ p258) ∨ (¬ p542) ∨ (¬ p41) ∨ (¬ p63) ∨ (¬ p424)) : (¬ p258) ∨ (¬ p542) ∨ p134 ∨ (¬ p4) ∨ p8 ∨ p12 ∨ (¬ p345) ∨ (¬ p656) ∨ (¬ p63) ∨ (¬ p41) ∨ (¬ p124) ∨ (¬ p424) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p345 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p656 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))
  have u12 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u13 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u14 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26611 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (q0 u12)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u13)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u14)
  · exact False.elim (q7 u0)
  · exact False.elim (q8 u1)
  · exact False.elim (q9 u9)
  · exact False.elim (q10 u8)
  · exact False.elim (q11 u11)

theorem step34873 (p12 p14 p41 p63 p124 p258 p268 p424 p542 p836 p1036 : Prop)
    (h26907 : p1036 ∨ p12)
    (h26612 : (¬ p124) ∨ (¬ p268) ∨ (¬ p836) ∨ (¬ p1036) ∨ (¬ p14) ∨ (¬ p258) ∨ (¬ p542) ∨ (¬ p41) ∨ (¬ p63) ∨ (¬ p424)) : (¬ p836) ∨ (¬ p258) ∨ (¬ p424) ∨ (¬ p124) ∨ (¬ p14) ∨ (¬ p268) ∨ (¬ p542) ∨ (¬ p41) ∨ (¬ p63) ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p268 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h26612 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u8)
  · exact False.elim (q9 u2)

theorem step34874 (p41 p63 p125 p303 p419 p422 p996 p1256 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26904 : (¬ p419) ∨ (¬ p996))
    (h26929 : p1256 ∨ p422)
    (h26613 : (¬ p1256) ∨ (¬ p1333) ∨ (¬ p303) ∨ (¬ p125) ∨ p996 ∨ (¬ p41) ∨ (¬ p63)) : p1325 ∨ (¬ p303) ∨ (¬ p63) ∨ (¬ p41) ∨ (¬ p125) ∨ (¬ p419) ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1325) := fun hu => hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : (¬ p996) := by
    rcases h26904 with q0 | q1
    · exact False.elim (q0 u5)
    · exact q1
  have u9 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h26613 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)
  · exact False.elim (u8 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u2)

theorem step34878 (p101 p102 p124 p125 p225 p304 p344 p362 p544 : Prop)
    (h26859 : p304 ∨ p124)
    (h26836 : (¬ p101) ∨ (¬ p102))
    (h26876 : (¬ p225) ∨ (¬ p544))
    (h26865 : p362 ∨ p125)
    (h26623 : p544 ∨ (¬ p304) ∨ (¬ p344) ∨ p102 ∨ (¬ p362)) : p124 ∨ (¬ p101) ∨ (¬ p225) ∨ (¬ p344) ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p101 := by
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
  have u4 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : (¬ p102) := by
    rcases h26836 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  have u7 : (¬ p544) := by
    rcases h26876 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u8 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h26623 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u8)

theorem step34880 (p41 p63 p125 p134 p142 p362 : Prop)
    (h26865 : p362 ∨ p125)
    (h26841 : p142 ∨ p134)
    (h26628 : (¬ p41) ∨ (¬ p63) ∨ (¬ p142) ∨ (¬ p362)) : (¬ p41) ∨ p125 ∨ p134 ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p125) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h26628 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step34882 (p5 p16 p422 p665 p789 p790 p814 p858 p1015 p1095 p1096 p1140 p1159 p1256 p1311 p1325 p1333 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26897 : p858 ∨ p789)
    (h26929 : p1256 ∨ p422)
    (h26931 : p1333 ∨ p1325)
    (h26893 : p814 ∨ p790)
    (h26630 : (¬ p1333) ∨ (¬ p1015) ∨ (¬ p858) ∨ (¬ p1256) ∨ (¬ p665) ∨ (¬ p1159) ∨ (¬ p1096) ∨ (¬ p1311) ∨ (¬ p1095) ∨ (¬ p5) ∨ (¬ p814) ∨ (¬ p16)) : p1140 ∨ (¬ p1015) ∨ p789 ∨ p422 ∨ (¬ p665) ∨ p1325 ∨ (¬ p1096) ∨ (¬ p1311) ∨ (¬ p1095) ∨ (¬ p5) ∨ p790 ∨ (¬ p16) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1311 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))
  have u12 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u13 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u14 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u15 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u16 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u10 q1)
  rcases h26630 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (q0 u15)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u13)
  · exact False.elim (q3 u14)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u12)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u8)
  · exact False.elim (q9 u9)
  · exact False.elim (q10 u16)
  · exact False.elim (q11 u11)

theorem step34883 (p41 p63 p124 p125 p134 p142 p163 p167 p304 p362 : Prop)
    (h26859 : p304 ∨ p124)
    (h26843 : p167 ∨ p163)
    (h26865 : p362 ∨ p125)
    (h26841 : p142 ∨ p134)
    (h26631 : (¬ p362) ∨ (¬ p167) ∨ (¬ p304) ∨ p41 ∨ (¬ p63) ∨ (¬ p142)) : p124 ∨ p163 ∨ (¬ p63) ∨ p125 ∨ p41 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26631 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u6)
  · exact False.elim (u4 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u9)

theorem step34884 (p2 p6 p38 p43 p63 p134 p142 p188 p303 p351 p387 p420 p595 p601 p789 p858 p897 p904 p918 p928 : Prop)
    (h26897 : p858 ∨ p789)
    (h26880 : (¬ p420) ∨ (¬ p601))
    (h26867 : p387 ∨ p303)
    (h26900 : (¬ p918) ∨ (¬ p928))
    (h26841 : p142 ∨ p134)
    (h26899 : p904 ∨ p897)
    (h26633 : (¬ p387) ∨ (¬ p595) ∨ p601 ∨ (¬ p38) ∨ (¬ p2) ∨ (¬ p6) ∨ (¬ p858) ∨ (¬ p43) ∨ p928 ∨ (¬ p63) ∨ (¬ p351) ∨ (¬ p142) ∨ (¬ p904) ∨ (¬ p188)) : (¬ p2) ∨ p789 ∨ (¬ p420) ∨ (¬ p38) ∨ (¬ p595) ∨ p303 ∨ (¬ p6) ∨ (¬ p43) ∨ (¬ p918) ∨ (¬ p63) ∨ (¬ p351) ∨ p134 ∨ p897 ∨ (¬ p188) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p789) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))))
  have u14 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u15 : (¬ p601) := by
    rcases h26880 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u16 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u17 : (¬ p928) := by
    rcases h26900 with q0 | q1
    · exact False.elim (q0 u8)
    · exact q1
  have u18 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  have u19 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u12 q1)
  rcases h26633 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13
  · exact False.elim (q0 u16)
  · exact False.elim (q1 u4)
  · exact False.elim (u15 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u14)
  · exact False.elim (q7 u7)
  · exact False.elim (u17 q8)
  · exact False.elim (q9 u9)
  · exact False.elim (q10 u10)
  · exact False.elim (q11 u18)
  · exact False.elim (q12 u19)
  · exact False.elim (q13 u13)

theorem step34885 (p6 p63 p125 p134 p142 p163 p167 p351 p422 p713 p789 p858 p882 p897 p904 p1140 p1159 p1256 : Prop)
    (h26897 : p858 ∨ p789)
    (h26841 : p142 ∨ p134)
    (h26899 : p904 ∨ p897)
    (h26843 : p167 ∨ p163)
    (h26919 : p1159 ∨ p1140)
    (h26929 : p1256 ∨ p422)
    (h26634 : (¬ p6) ∨ (¬ p858) ∨ (¬ p125) ∨ (¬ p63) ∨ (¬ p351) ∨ (¬ p142) ∨ (¬ p904) ∨ (¬ p882) ∨ (¬ p713) ∨ (¬ p167) ∨ (¬ p1159) ∨ (¬ p1256)) : (¬ p125) ∨ (¬ p351) ∨ p789 ∨ (¬ p6) ∨ (¬ p63) ∨ p134 ∨ p897 ∨ (¬ p882) ∨ (¬ p713) ∨ p163 ∨ p1140 ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p882 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p713 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))
  have u12 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u13 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u14 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u15 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  have u16 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u10 q1)
  have u17 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  rcases h26634 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u12)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u13)
  · exact False.elim (q6 u14)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u8)
  · exact False.elim (q9 u15)
  · exact False.elim (q10 u16)
  · exact False.elim (q11 u17)

theorem step34886 (p6 p15 p43 p63 p71 p105 p127 p880 p918 p928 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26839 : p127 ∨ p6)
    (h26900 : (¬ p918) ∨ (¬ p928))
    (h26635 : (¬ p1099) ∨ (¬ p71) ∨ (¬ p15) ∨ (¬ p127) ∨ (¬ p43) ∨ p928 ∨ (¬ p63) ∨ (¬ p105) ∨ (¬ p880)) : (¬ p880) ∨ p1096 ∨ (¬ p15) ∨ (¬ p71) ∨ p6 ∨ (¬ p918) ∨ (¬ p43) ∨ (¬ p105) ∨ (¬ p63) := by
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
  have u3 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : (¬ p928) := by
    rcases h26900 with q0 | q1
    · exact False.elim (q0 u5)
    · exact q1
  rcases h26635 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u6)
  · exact False.elim (u11 q5)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u0)

theorem step34888 (p1 p2 p6 p105 p127 p303 p382 p387 : Prop)
    (h26839 : p127 ∨ p6)
    (h26867 : p387 ∨ p303)
    (h26637 : (¬ p2) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p1) ∨ (¬ p105) ∨ (¬ p127)) : (¬ p2) ∨ p6 ∨ p303 ∨ (¬ p382) ∨ (¬ p105) ∨ (¬ p1) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h26637 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)

theorem step34889 (p2 p303 p327 p387 p419 p481 p996 p1140 p1159 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26867 : p387 ∨ p303)
    (h26904 : (¬ p419) ∨ (¬ p996))
    (h26873 : p481 ∨ p2)
    (h26638 : (¬ p1159) ∨ p996 ∨ (¬ p481) ∨ (¬ p327) ∨ (¬ p387)) : p1140 ∨ p303 ∨ (¬ p419) ∨ (¬ p327) ∨ p2 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p327 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : (¬ p996) := by
    rcases h26904 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u8 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h26638 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)

theorem step34893 (p3 p17 p134 p163 p188 p189 p226 : Prop)
    (h26847 : p226 ∨ p3)
    (h26642 : p17 ∨ (¬ p226) ∨ p134 ∨ (¬ p188) ∨ (¬ p189) ∨ (¬ p163)) : p3 ∨ p17 ∨ (¬ p163) ∨ (¬ p188) ∨ (¬ p189) ∨ p134 := by
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
  have u4 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h26642 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u2)

theorem step34894 (p12 p14 p229 p423 p940 p1036 : Prop)
    (h26906 : (¬ p12) ∨ (¬ p1036))
    (h26849 : p229 ∨ p14)
    (h26643 : (¬ p940) ∨ (¬ p423) ∨ p1036 ∨ (¬ p229)) : (¬ p940) ∨ (¬ p423) ∨ (¬ p12) ∨ p14 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p1036) := by
    rcases h26906 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u5 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h26643 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u4 q2)
  · exact False.elim (q3 u5)

theorem step34899 (p3 p14 p163 p167 p303 p382 p406 p419 p996 : Prop)
    (h26904 : (¬ p419) ∨ (¬ p996))
    (h26868 : (¬ p382) ∨ (¬ p406))
    (h26842 : (¬ p163) ∨ (¬ p167))
    (h26650 : p167 ∨ p996 ∨ (¬ p3) ∨ p14 ∨ p406 ∨ p303) : p303 ∨ p14 ∨ (¬ p3) ∨ (¬ p419) ∨ (¬ p382) ∨ (¬ p163) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p14) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p996) := by
    rcases h26904 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  have u7 : (¬ p406) := by
    rcases h26868 with q0 | q1
    · exact False.elim (q0 u4)
    · exact q1
  have u8 : (¬ p167) := by
    rcases h26842 with q0 | q1
    · exact False.elim (q0 u5)
    · exact q1
  rcases h26650 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u8 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (u1 q3)
  · exact False.elim (u7 q4)
  · exact False.elim (u0 q5)

theorem step34900 (p3 p63 p104 p195 p225 p303 p382 p387 p406 p918 p928 : Prop)
    (h26901 : p928 ∨ p918)
    (h26868 : (¬ p382) ∨ (¬ p406))
    (h26867 : p387 ∨ p303)
    (h26651 : p225 ∨ (¬ p928) ∨ (¬ p195) ∨ (¬ p104) ∨ (¬ p63) ∨ (¬ p3) ∨ p406 ∨ (¬ p387)) : (¬ p104) ∨ p225 ∨ p918 ∨ (¬ p195) ∨ (¬ p63) ∨ (¬ p3) ∨ (¬ p382) ∨ p303 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : (¬ p406) := by
    rcases h26868 with q0 | q1
    · exact False.elim (q0 u6)
    · exact q1
  have u10 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h26651 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (u9 q6)
  · exact False.elim (q7 u10)

theorem step34901 (p224 p303 p344 p349 p387 p836 p840 : Prop)
    (h26894 : (¬ p836) ∨ (¬ p840))
    (h26867 : p387 ∨ p303)
    (h26652 : p840 ∨ (¬ p224) ∨ (¬ p349) ∨ (¬ p344) ∨ (¬ p387)) : (¬ p836) ∨ p303 ∨ (¬ p224) ∨ (¬ p349) ∨ (¬ p344) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p840) := by
    rcases h26894 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u6 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h26652 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u6)

theorem step34902 (p303 p349 p387 p663 p1076 p1077 : Prop)
    (h26867 : p387 ∨ p303)
    (h26910 : (¬ p1076) ∨ (¬ p1077))
    (h26653 : p1077 ∨ (¬ p663) ∨ (¬ p349) ∨ (¬ p387)) : (¬ p663) ∨ p303 ∨ (¬ p1076) ∨ (¬ p349) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p663 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : (¬ p1077) := by
    rcases h26910 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h26653 with q0 | q1 | q2 | q3
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step34903 (p14 p229 p886 : Prop)
    (h26848 : (¬ p14) ∨ (¬ p229))
    (h26665 : p886 ∨ p229) : p886 ∨ (¬ p14) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p886) := fun hu => hn (Or.inl hu)
  have u1 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p229) := by
    rcases h26848 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h26665 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step34904 (p225 p595 p886 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26655 : (¬ p595) ∨ (¬ p1099) ∨ (¬ p886) ∨ (¬ p225)) : p1096 ∨ (¬ p225) ∨ (¬ p595) ∨ (¬ p886) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1096) := fun hu => hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p886 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h26655 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)

theorem step34912 (p8 p16 p234 p303 p327 p351 p387 p789 p790 p814 p858 p1096 p1099 : Prop)
    (h26867 : p387 ∨ p303)
    (h26893 : p814 ∨ p790)
    (h26897 : p858 ∨ p789)
    (h26912 : (¬ p1096) ∨ (¬ p1099))
    (h26666 : (¬ p814) ∨ p1099 ∨ (¬ p16) ∨ (¬ p858) ∨ (¬ p234) ∨ (¬ p8) ∨ (¬ p351) ∨ (¬ p327) ∨ (¬ p387)) : p303 ∨ p790 ∨ (¬ p16) ∨ p789 ∨ (¬ p1096) ∨ (¬ p8) ∨ (¬ p234) ∨ (¬ p327) ∨ (¬ p351) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p790) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p327 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u11 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u12 : (¬ p1099) := by
    rcases h26912 with q0 | q1
    · exact False.elim (q0 u4)
    · exact q1
  rcases h26666 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u10)
  · exact False.elim (u12 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u9)

theorem step34915 (p8 p106 p172 p225 p303 p420 p579 p582 p595 p616 p789 p836 p840 p858 p918 p928 p1076 p1077 p1287 : Prop)
    (h26897 : p858 ∨ p789)
    (h26883 : p616 ∨ p595)
    (h26895 : p840 ∨ p836)
    (h26911 : p1077 ∨ p1076)
    (h26901 : p928 ∨ p918)
    (h26674 : (¬ p1077) ∨ (¬ p420) ∨ (¬ p582) ∨ (¬ p579) ∨ (¬ p616) ∨ (¬ p1287) ∨ (¬ p840) ∨ (¬ p106) ∨ (¬ p172) ∨ (¬ p928) ∨ (¬ p8) ∨ (¬ p858) ∨ (¬ p303) ∨ (¬ p225)) : (¬ p172) ∨ (¬ p420) ∨ (¬ p582) ∨ p789 ∨ p595 ∨ (¬ p1287) ∨ (¬ p106) ∨ (¬ p579) ∨ p836 ∨ p1076 ∨ p918 ∨ (¬ p8) ∨ (¬ p303) ∨ (¬ p225) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p172 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p579 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))))
  have u14 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u15 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u16 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u17 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  have u18 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u10 q1)
  rcases h26674 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13
  · exact False.elim (q0 u17)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u15)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u16)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u0)
  · exact False.elim (q9 u18)
  · exact False.elim (q10 u11)
  · exact False.elim (q11 u14)
  · exact False.elim (q12 u12)
  · exact False.elim (q13 u13)

theorem step34918 (p103 p106 p225 p344 p346 p420 p601 : Prop)
    (h26862 : (¬ p344) ∨ (¬ p346))
    (h26881 : p601 ∨ p420)
    (h26680 : p346 ∨ (¬ p103) ∨ (¬ p106) ∨ (¬ p601) ∨ (¬ p225)) : (¬ p103) ∨ (¬ p344) ∨ p420 ∨ (¬ p225) ∨ (¬ p106) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p346) := by
    rcases h26862 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  have u6 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h26680 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)

theorem step34920 (p8 p12 p14 p41 p63 p101 p158 p187 p189 p225 p228 p576 p581 p789 p790 p814 p858 p897 : Prop)
    (h26893 : p814 ∨ p790)
    (h26897 : p858 ∨ p789)
    (h26879 : p581 ∨ p576)
    (h26682 : p101 ∨ (¬ p581) ∨ (¬ p41) ∨ (¬ p14) ∨ p897 ∨ p63 ∨ p12 ∨ (¬ p858) ∨ (¬ p814) ∨ (¬ p187) ∨ (¬ p189) ∨ (¬ p8) ∨ (¬ p228) ∨ (¬ p158) ∨ (¬ p225)) : p897 ∨ p63 ∨ p101 ∨ (¬ p14) ∨ (¬ p158) ∨ p790 ∨ p12 ∨ p789 ∨ (¬ p41) ∨ (¬ p187) ∨ (¬ p189) ∨ (¬ p8) ∨ p576 ∨ (¬ p228) ∨ (¬ p225) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p897) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p63) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))))))
  have u15 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u16 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u17 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u12 q1)
  rcases h26682 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u17)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u3)
  · exact False.elim (u0 q4)
  · exact False.elim (u1 q5)
  · exact False.elim (u6 q6)
  · exact False.elim (q7 u16)
  · exact False.elim (q8 u15)
  · exact False.elim (q9 u9)
  · exact False.elim (q10 u10)
  · exact False.elim (q11 u11)
  · exact False.elim (q12 u13)
  · exact False.elim (q13 u4)
  · exact False.elim (q14 u14)

theorem step34921 (p101 p224 p344 p346 p495 p897 p904 : Prop)
    (h26863 : p346 ∨ p344)
    (h26899 : p904 ∨ p897)
    (h26683 : (¬ p346) ∨ (¬ p101) ∨ (¬ p904) ∨ (¬ p224) ∨ (¬ p495)) : p344 ∨ (¬ p101) ∨ p897 ∨ (¬ p224) ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p344) := fun hu => hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h26683 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)

theorem step34924 (p106 p225 p662 p980 p983 p1452 : Prop)
    (h26902 : (¬ p980) ∨ (¬ p983))
    (h26686 : p983 ∨ (¬ p1452) ∨ (¬ p662) ∨ (¬ p106) ∨ (¬ p225)) : (¬ p980) ∨ (¬ p1452) ∨ (¬ p662) ∨ (¬ p106) ∨ (¬ p225) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p662 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p983) := by
    rcases h26902 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h26686 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)

theorem step34936 (p6 p10 p63 p85 p127 p234 p303 p323 p344 p419 p642 p897 p903 p904 p996 p1055 p1061 p1076 p1229 p1232 p1311 p1387 : Prop)
    (h26839 : p127 ∨ p6)
    (h26861 : p323 ∨ p10)
    (h26909 : p1061 ∨ p1055)
    (h26835 : p85 ∨ p63)
    (h26905 : p996 ∨ p419)
    (h26899 : p904 ∨ p897)
    (h26927 : p1232 ∨ p1229)
    (h26713 : (¬ p127) ∨ (¬ p996) ∨ p303 ∨ (¬ p323) ∨ p344 ∨ (¬ p642) ∨ (¬ p1311) ∨ (¬ p1061) ∨ (¬ p1387) ∨ (¬ p85) ∨ (¬ p234) ∨ (¬ p903) ∨ (¬ p904) ∨ (¬ p1232) ∨ (¬ p1076)) : p303 ∨ (¬ p1076) ∨ p6 ∨ p10 ∨ p344 ∨ (¬ p642) ∨ (¬ p1311) ∨ p1055 ∨ (¬ p1387) ∨ p63 ∨ p419 ∨ (¬ p903) ∨ p897 ∨ p1229 ∨ (¬ p234) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p642 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1311 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p903 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))))))
  have u15 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u16 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u17 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u18 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  have u19 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u10 q1)
  have u20 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u12 q1)
  have u21 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u13 q1)
  rcases h26713 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14
  · exact False.elim (q0 u15)
  · exact False.elim (q1 u19)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u16)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u17)
  · exact False.elim (q8 u8)
  · exact False.elim (q9 u18)
  · exact False.elim (q10 u14)
  · exact False.elim (q11 u11)
  · exact False.elim (q12 u20)
  · exact False.elim (q13 u21)
  · exact False.elim (q14 u1)

theorem step34942 (p15 p41 p63 p163 p167 p224 p225 p563 p595 p616 p657 p897 p1076 p1095 p1115 : Prop)
    (h26883 : p616 ∨ p595)
    (h26842 : (¬ p163) ∨ (¬ p167))
    (h26886 : (¬ p224) ∨ (¬ p657))
    (h26719 : p1115 ∨ (¬ p616) ∨ p15 ∨ (¬ p563) ∨ p897 ∨ (¬ p1095) ∨ p657 ∨ p63 ∨ (¬ p1076) ∨ p167 ∨ (¬ p41) ∨ (¬ p225)) : (¬ p1095) ∨ p897 ∨ (¬ p41) ∨ p15 ∨ p595 ∨ (¬ p563) ∨ (¬ p225) ∨ p63 ∨ p1115 ∨ (¬ p163) ∨ (¬ p224) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p897) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p563 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))
  have u12 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u13 : (¬ p167) := by
    rcases h26842 with q0 | q1
    · exact False.elim (q0 u9)
    · exact q1
  have u14 : (¬ p657) := by
    rcases h26886 with q0 | q1
    · exact False.elim (q0 u10)
    · exact q1
  rcases h26719 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u12)
  · exact False.elim (u3 q2)
  · exact False.elim (q3 u5)
  · exact False.elim (u1 q4)
  · exact False.elim (q5 u0)
  · exact False.elim (u14 q6)
  · exact False.elim (u7 q7)
  · exact False.elim (q8 u11)
  · exact False.elim (u13 q9)
  · exact False.elim (q10 u2)
  · exact False.elim (q11 u6)

theorem step34943 (p8 p14 p86 p101 p186 p189 p193 p224 p225 p228 p229 p422 p576 p581 p595 p616 p642 p657 p897 p903 p904 p1079 p1095 p1098 p1256 : Prop)
    (h26929 : p1256 ∨ p422)
    (h26886 : (¬ p224) ∨ (¬ p657))
    (h26879 : p581 ∨ p576)
    (h26845 : p193 ∨ p189)
    (h26899 : p904 ∨ p897)
    (h26883 : p616 ∨ p595)
    (h26848 : (¬ p14) ∨ (¬ p229))
    (h26720 : (¬ p8) ∨ (¬ p581) ∨ (¬ p186) ∨ (¬ p193) ∨ p101 ∨ (¬ p228) ∨ (¬ p616) ∨ (¬ p1256) ∨ (¬ p1098) ∨ (¬ p642) ∨ (¬ p903) ∨ (¬ p904) ∨ (¬ p1095) ∨ p657 ∨ (¬ p86) ∨ (¬ p1079) ∨ p229 ∨ (¬ p225)) : (¬ p1095) ∨ p422 ∨ (¬ p224) ∨ p576 ∨ p101 ∨ (¬ p228) ∨ p189 ∨ (¬ p186) ∨ (¬ p1098) ∨ (¬ p642) ∨ (¬ p903) ∨ p897 ∨ (¬ p8) ∨ p595 ∨ (¬ p86) ∨ (¬ p1079) ∨ (¬ p14) ∨ (¬ p225) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p422) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1098 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p642 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p903 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))
  have u15 : p1079 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))
  have u16 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))
  have u17 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))))))))
  have u18 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u19 : (¬ p657) := by
    rcases h26886 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u20 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u21 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u22 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  have u23 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u13 q1)
  have u24 : (¬ p229) := by
    rcases h26848 with q0 | q1
    · exact False.elim (q0 u16)
    · exact q1
  rcases h26720 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14 | q15 | q16 | q17
  · exact False.elim (q0 u12)
  · exact False.elim (q1 u20)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u21)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u23)
  · exact False.elim (q7 u18)
  · exact False.elim (q8 u8)
  · exact False.elim (q9 u9)
  · exact False.elim (q10 u10)
  · exact False.elim (q11 u22)
  · exact False.elim (q12 u0)
  · exact False.elim (u19 q13)
  · exact False.elim (q14 u14)
  · exact False.elim (q15 u15)
  · exact False.elim (u24 q16)
  · exact False.elim (q17 u17)

theorem step34944 (p4 p8 p86 p101 p102 p134 p189 p193 p345 p576 p581 p642 p710 p897 p904 : Prop)
    (h26889 : p710 ∨ p8)
    (h26879 : p581 ∨ p576)
    (h26845 : p193 ∨ p189)
    (h26837 : p102 ∨ p101)
    (h26899 : p904 ∨ p897)
    (h26721 : p134 ∨ (¬ p581) ∨ (¬ p86) ∨ (¬ p710) ∨ (¬ p193) ∨ (¬ p642) ∨ (¬ p4) ∨ (¬ p345) ∨ (¬ p102) ∨ (¬ p904)) : p8 ∨ p576 ∨ (¬ p86) ∨ (¬ p345) ∨ p134 ∨ (¬ p4) ∨ (¬ p642) ∨ p189 ∨ p101 ∨ p897 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p8) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p345 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p642 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u11 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u12 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u13 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u14 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h26721 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u11)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u12)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u3)
  · exact False.elim (q8 u13)
  · exact False.elim (q9 u14)

theorem step34945 (p18 p101 p102 p134 p136 p258 : Prop)
    (h26837 : p102 ∨ p101)
    (h26743 : p18 ∨ (¬ p258) ∨ (¬ p136) ∨ (¬ p134) ∨ (¬ p102)) : p101 ∨ (¬ p258) ∨ (¬ p134) ∨ p18 ∨ (¬ p136) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p101) := fun hu => hn (Or.inl hu)
  have u1 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p136 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h26743 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step34946 (p8 p17 p101 p102 p163 p167 p185 p189 p224 p256 p710 p1325 : Prop)
    (h26853 : p256 ∨ p17)
    (h26842 : (¬ p163) ∨ (¬ p167))
    (h26837 : p102 ∨ p101)
    (h26889 : p710 ∨ p8)
    (h26745 : p185 ∨ p167 ∨ (¬ p189) ∨ (¬ p102) ∨ (¬ p256) ∨ (¬ p1325) ∨ (¬ p224) ∨ (¬ p710)) : p17 ∨ p185 ∨ (¬ p163) ∨ p101 ∨ (¬ p189) ∨ (¬ p1325) ∨ (¬ p224) ∨ p8 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p17) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : (¬ p167) := by
    rcases h26842 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u10 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h26745 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u1 q0)
  · exact False.elim (u9 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u11)

theorem step34947 (p8 p17 p256 p344 p346 p710 p897 p904 p1095 p1287 p1325 p1644 : Prop)
    (h26899 : p904 ∨ p897)
    (h26863 : p346 ∨ p344)
    (h26853 : p256 ∨ p17)
    (h26889 : p710 ∨ p8)
    (h26746 : (¬ p346) ∨ (¬ p1095) ∨ (¬ p1644) ∨ (¬ p256) ∨ (¬ p1325) ∨ (¬ p1287) ∨ (¬ p710) ∨ (¬ p904)) : (¬ p1644) ∨ p897 ∨ p344 ∨ (¬ p1095) ∨ p17 ∨ (¬ p1287) ∨ p8 ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1644 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p897) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h26746 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u11)
  · exact False.elim (q7 u8)

theorem step34949 (p8 p101 p102 p134 p185 p224 p657 p710 p897 p904 p980 p983 p1325 : Prop)
    (h26899 : p904 ∨ p897)
    (h26837 : p102 ∨ p101)
    (h26902 : (¬ p980) ∨ (¬ p983))
    (h26889 : p710 ∨ p8)
    (h26886 : (¬ p224) ∨ (¬ p657))
    (h26748 : p185 ∨ p983 ∨ (¬ p1325) ∨ p657 ∨ (¬ p102) ∨ p134 ∨ (¬ p710) ∨ (¬ p904)) : p897 ∨ p101 ∨ (¬ p980) ∨ p8 ∨ (¬ p224) ∨ (¬ p1325) ∨ p134 ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p897) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p101) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : (¬ p983) := by
    rcases h26902 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u11 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u12 : (¬ p657) := by
    rcases h26886 with q0 | q1
    · exact False.elim (q0 u4)
    · exact q1
  rcases h26748 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (u10 q1)
  · exact False.elim (q2 u5)
  · exact False.elim (u12 q3)
  · exact False.elim (q4 u9)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u11)
  · exact False.elim (q7 u8)

theorem step34951 (p8 p240 p710 p918 p1385 p1393 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h26889 : p710 ∨ p8)
    (h26750 : (¬ p1393) ∨ (¬ p918) ∨ (¬ p240) ∨ (¬ p710)) : (¬ p240) ∨ p1385 ∨ p8 ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p240 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1385) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h26750 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)

theorem step34952 (p11 p121 p134 p532 p1206 p1508 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26751 : (¬ p1206) ∨ (¬ p532) ∨ (¬ p1508) ∨ p11 ∨ p134) : (¬ p1508) ∨ p121 ∨ p11 ∨ (¬ p532) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p121) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h26751 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (u2 q3)
  · exact False.elim (u4 q4)

theorem step34954 (p12 p101 p102 p121 p1036 : Prop)
    (h26836 : (¬ p101) ∨ (¬ p102))
    (h26907 : p1036 ∨ p12)
    (h26764 : p102 ∨ (¬ p121) ∨ (¬ p1036)) : (¬ p101) ∨ p12 ∨ (¬ p121) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p102) := by
    rcases h26836 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u4 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h26764 with q0 | q1 | q2
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)

theorem step34960 (p918 p928 p1122 p1273 : Prop)
    (h26901 : p928 ∨ p918)
    (h26774 : p1273 ∨ (¬ p928) ∨ (¬ p1122)) : p1273 ∨ p918 ∨ (¬ p1122) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1273) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1122 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h26774 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)

theorem step34962 (p87 p224 p258 p288 p344 p576 p581 p657 : Prop)
    (h26887 : p657 ∨ p224)
    (h26879 : p581 ∨ p576)
    (h26855 : p288 ∨ p258)
    (h26776 : (¬ p657) ∨ (¬ p581) ∨ (¬ p344) ∨ (¬ p288) ∨ (¬ p87)) : (¬ p344) ∨ p224 ∨ p576 ∨ p258 ∨ (¬ p87) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h26776 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u4)

theorem step34963 (p980 p983 p1313 : Prop)
    (h26902 : (¬ p980) ∨ (¬ p983))
    (h26784 : p1313 ∨ p983) : p1313 ∨ (¬ p980) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1313) := fun hu => hn (Or.inl hu)
  have u1 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p983) := by
    rcases h26902 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h26784 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step34964 (p17 p63 p85 p256 p258 p288 p595 p1076 p1077 p1229 p1232 p1313 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h26853 : p256 ∨ p17)
    (h26855 : p288 ∨ p258)
    (h26835 : p85 ∨ p63)
    (h26911 : p1077 ∨ p1076)
    (h26785 : (¬ p595) ∨ (¬ p1232) ∨ (¬ p288) ∨ (¬ p256) ∨ (¬ p85) ∨ (¬ p1313) ∨ (¬ p1077)) : p1229 ∨ p17 ∨ p258 ∨ (¬ p595) ∨ p63 ∨ (¬ p1313) ∨ p1076 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1229) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1313 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h26785 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u11)

theorem step34965 (p63 p85 p1394 : Prop)
    (h26835 : p85 ∨ p63)
    (h26786 : p1394 ∨ (¬ p85)) : p1394 ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1394) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p63) := fun hu => hn (Or.inr hu)
  have u2 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h26786 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)

theorem step34966 (p17 p86 p161 p256 p258 p288 p344 p346 p595 p616 p633 p980 p1076 p1077 p1225 : Prop)
    (h26862 : (¬ p344) ∨ (¬ p346))
    (h26925 : p1225 ∨ p161)
    (h26883 : p616 ∨ p595)
    (h26855 : p288 ∨ p258)
    (h26853 : p256 ∨ p17)
    (h26911 : p1077 ∨ p1076)
    (h26788 : p346 ∨ (¬ p616) ∨ (¬ p1225) ∨ (¬ p633) ∨ (¬ p288) ∨ (¬ p256) ∨ (¬ p86) ∨ (¬ p1077) ∨ (¬ p980)) : (¬ p344) ∨ p161 ∨ p595 ∨ (¬ p633) ∨ p258 ∨ p17 ∨ (¬ p86) ∨ p1076 ∨ (¬ p980) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p161) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p346) := by
    rcases h26862 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u10 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u11 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u12 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u13 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u14 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h26788 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u11)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u12)
  · exact False.elim (q5 u13)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u14)
  · exact False.elim (q8 u8)

theorem step34973 (p6 p18 p19 p25 p124 p127 p304 p633 : Prop)
    (h26859 : p304 ∨ p124)
    (h26838 : (¬ p6) ∨ (¬ p127))
    (h26829 : p19 ∨ p18)
    (h26796 : p127 ∨ (¬ p304) ∨ (¬ p633) ∨ (¬ p25) ∨ (¬ p19)) : p124 ∨ (¬ p633) ∨ (¬ p25) ∨ (¬ p6) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p25 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : (¬ p127) := by
    rcases h26838 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  have u7 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h26796 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u7)

theorem step34975 (p15 p47 p63 p64 p68 p69 p85 p186 p189 p193 p258 p421 p495 p496 p595 p1076 p1077 p1229 p1232 p1313 : Prop)
    (h26845 : p193 ∨ p189)
    (h26833 : p69 ∨ p15)
    (h26835 : p85 ∨ p63)
    (h26927 : p1232 ∨ p1229)
    (h26911 : p1077 ∨ p1076)
    (h26798 : (¬ p595) ∨ (¬ p258) ∨ (¬ p496) ∨ (¬ p495) ∨ (¬ p421) ∨ (¬ p186) ∨ (¬ p193) ∨ (¬ p69) ∨ (¬ p68) ∨ (¬ p64) ∨ (¬ p85) ∨ (¬ p47) ∨ (¬ p1232) ∨ (¬ p1313) ∨ (¬ p1077)) : (¬ p258) ∨ (¬ p496) ∨ (¬ p595) ∨ (¬ p495) ∨ (¬ p421) ∨ (¬ p186) ∨ p189 ∨ p15 ∨ (¬ p68) ∨ (¬ p64) ∨ p63 ∨ (¬ p47) ∨ p1229 ∨ (¬ p1313) ∨ p1076 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p496 := by
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
  have u4 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : p1313 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))))))
  have u15 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u16 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u17 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u10 q1)
  have u18 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u12 q1)
  have u19 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u14 q1)
  rcases h26798 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u15)
  · exact False.elim (q7 u16)
  · exact False.elim (q8 u8)
  · exact False.elim (q9 u9)
  · exact False.elim (q10 u17)
  · exact False.elim (q11 u11)
  · exact False.elim (q12 u18)
  · exact False.elim (q13 u13)
  · exact False.elim (q14 u19)

theorem step34976 (p134 p142 p163 p633 : Prop)
    (h26841 : p142 ∨ p134)
    (h26799 : p163 ∨ (¬ p142) ∨ (¬ p633)) : p163 ∨ (¬ p633) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p163) := fun hu => hn (Or.inl hu)
  have u1 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h26799 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)

theorem step34977 (p11 p124 p126 p532 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26800 : (¬ p532) ∨ (¬ p1333) ∨ (¬ p11) ∨ (¬ p126) ∨ (¬ p124)) : (¬ p532) ∨ p1325 ∨ (¬ p11) ∨ (¬ p126) ∨ (¬ p124) := by
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
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h26800 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)

theorem step34982 (p10 p101 p102 p124 p134 p142 p304 p323 p345 : Prop)
    (h26859 : p304 ∨ p124)
    (h26837 : p102 ∨ p101)
    (h26841 : p142 ∨ p134)
    (h26861 : p323 ∨ p10)
    (h26805 : (¬ p304) ∨ (¬ p345) ∨ (¬ p102) ∨ (¬ p142) ∨ (¬ p323)) : p124 ∨ (¬ p345) ∨ p101 ∨ p134 ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p345 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h26805 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)

theorem step34984 (p2 p6 p124 p134 p142 p304 p368 p424 p1287 : Prop)
    (h26858 : (¬ p124) ∨ (¬ p304))
    (h26841 : p142 ∨ p134)
    (h26808 : (¬ p2) ∨ (¬ p6) ∨ (¬ p1287) ∨ (¬ p368) ∨ p304 ∨ (¬ p424) ∨ (¬ p142)) : (¬ p2) ∨ (¬ p124) ∨ (¬ p1287) ∨ (¬ p6) ∨ (¬ p368) ∨ (¬ p424) ∨ p134 := by
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
  have u2 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p304) := by
    rcases h26858 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  have u8 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h26808 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (u7 q4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u8)

theorem step34986 (p18 p41 p43 p45 p134 p142 p163 p167 p918 : Prop)
    (h26831 : p45 ∨ p41)
    (h26842 : (¬ p163) ∨ (¬ p167))
    (h26841 : p142 ∨ p134)
    (h26810 : p918 ∨ (¬ p43) ∨ (¬ p45) ∨ (¬ p18) ∨ p167 ∨ (¬ p142)) : p918 ∨ (¬ p18) ∨ p41 ∨ (¬ p43) ∨ (¬ p163) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p918) := fun hu => hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : (¬ p167) := by
    rcases h26842 with q0 | q1
    · exact False.elim (q0 u4)
    · exact q1
  have u8 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26810 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (u7 q4)
  · exact False.elim (q5 u8)

theorem step34987 (p6 p10 p134 p142 p224 p225 p323 p544 p595 p616 p1287 : Prop)
    (h26883 : p616 ∨ p595)
    (h26876 : (¬ p225) ∨ (¬ p544))
    (h26841 : p142 ∨ p134)
    (h26861 : p323 ∨ p10)
    (h26811 : p224 ∨ (¬ p6) ∨ p544 ∨ (¬ p1287) ∨ (¬ p616) ∨ (¬ p142) ∨ (¬ p323)) : p224 ∨ p595 ∨ (¬ p6) ∨ (¬ p1287) ∨ (¬ p225) ∨ p134 ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p224) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p595) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : (¬ p544) := by
    rcases h26876 with q0 | q1
    · exact False.elim (q0 u4)
    · exact q1
  have u9 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h26811 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (u8 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u10)

theorem step34988 (p2 p6 p18 p63 p85 p134 p142 p481 p539 p542 : Prop)
    (h26835 : p85 ∨ p63)
    (h26841 : p142 ∨ p134)
    (h26873 : p481 ∨ p2)
    (h26812 : (¬ p85) ∨ (¬ p539) ∨ (¬ p18) ∨ (¬ p542) ∨ (¬ p142) ∨ (¬ p481) ∨ (¬ p6)) : p63 ∨ (¬ p539) ∨ (¬ p18) ∨ (¬ p542) ∨ p134 ∨ p2 ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p63) := fun hu => hn (Or.inl hu)
  have u1 : p539 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26812 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u6)

theorem step34989 (p6 p134 p142 p240 p709 p1000 p1074 p1115 p1116 p1140 p1226 p1325 p1333 p1349 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26915 : p1116 ∨ p1115)
    (h26841 : p142 ∨ p134)
    (h26813 : (¬ p1333) ∨ (¬ p1226) ∨ (¬ p1140) ∨ (¬ p1116) ∨ (¬ p240) ∨ (¬ p709) ∨ (¬ p1349) ∨ (¬ p1074) ∨ (¬ p1000) ∨ (¬ p142) ∨ (¬ p6)) : p1325 ∨ (¬ p1226) ∨ (¬ p1140) ∨ p1115 ∨ (¬ p240) ∨ (¬ p709) ∨ (¬ p1349) ∨ (¬ p1074) ∨ (¬ p1000) ∨ p134 ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1325) := fun hu => hn (Or.inl hu)
  have u1 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p240 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p709 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u12 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u13 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h26813 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u11)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u12)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u8)
  · exact False.elim (q9 u13)
  · exact False.elim (q10 u10)

theorem step34993 (p6 p18 p19 p39 p63 : Prop)
    (h26829 : p19 ∨ p18)
    (h26823 : (¬ p19) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p6)) : p18 ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p18) := fun hu => hn (Or.inl hu)
  have u1 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h26823 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)

theorem step34996 (p2 p6 p20 p134 p142 p481 p633 p636 : Prop)
    (h26885 : p636 ∨ p633)
    (h26841 : p142 ∨ p134)
    (h26873 : p481 ∨ p2)
    (h26826 : (¬ p636) ∨ (¬ p20) ∨ (¬ p142) ∨ (¬ p481) ∨ (¬ p6)) : p633 ∨ (¬ p20) ∨ p134 ∨ p2 ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : p20 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h26826 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u4)

theorem step34997 (p2 p6 p63 p85 p134 p142 p234 p481 p577 p662 p789 p833 p836 p840 p858 p1325 : Prop)
    (h26841 : p142 ∨ p134)
    (h26895 : p840 ∨ p836)
    (h26897 : p858 ∨ p789)
    (h26834 : (¬ p63) ∨ (¬ p85))
    (h26873 : p481 ∨ p2)
    (h26827 : (¬ p142) ∨ (¬ p662) ∨ (¬ p833) ∨ (¬ p840) ∨ (¬ p577) ∨ (¬ p858) ∨ (¬ p234) ∨ p85 ∨ (¬ p481) ∨ (¬ p1325) ∨ (¬ p6)) : p134 ∨ (¬ p662) ∨ (¬ p833) ∨ p836 ∨ (¬ p577) ∨ p789 ∨ (¬ p234) ∨ (¬ p63) ∨ p2 ∨ (¬ p1325) ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p134) := fun hu => hn (Or.inl hu)
  have u1 : p662 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p833 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u12 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u13 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u14 : (¬ p85) := by
    rcases h26834 with q0 | q1
    · exact False.elim (q0 u7)
    · exact q1
  have u15 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h26827 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u11)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u12)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u13)
  · exact False.elim (q6 u6)
  · exact False.elim (u14 q7)
  · exact False.elim (q8 u15)
  · exact False.elim (q9 u9)
  · exact False.elim (q10 u10)

theorem step35016 (p8 p709 p713 : Prop)
    (h29060 : (¬ p8) ∨ p713 ∨ p709)
    (h24573 : p709 ∨ p8 ∨ p713) : p713 ∨ p709 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p713) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p709) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p8) := by
    rcases h29060 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h24573 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (u0 q2)

theorem step35018 (p8 p224 p419 p1055 : Prop)
    (h34852 : (¬ p1055) ∨ (¬ p8) ∨ p419)
    (h34853 : p419 ∨ p8 ∨ (¬ p224)) : (¬ p1055) ∨ p419 ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p419) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p8) := by
    rcases h34852 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (u1 q2)
  rcases h34853 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u2)

theorem step35137 (p17 p84 p495 p576 : Prop)
    (h26954 : p17 ∨ (¬ p576) ∨ (¬ p84))
    (h22399 : p84 ∨ (¬ p495) ∨ p17) : p17 ∨ (¬ p576) ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p17) := fun hu => hn (Or.inl hu)
  have u1 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p84) := by
    rcases h26954 with q0 | q1 | q2
    · exact False.elim (u0 q0)
    · exact False.elim (q1 u1)
    · exact q2
  rcases h22399 with q0 | q1 | q2
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (u0 q2)

theorem step35154 (p121 p1207 p1211 : Prop)
    (h21670 : p1211 ∨ p1207 ∨ p121)
    (h31813 : p1211 ∨ p1207 ∨ (¬ p121)) : p1207 ∨ p1211 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1207) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1211) := fun hu => hn (Or.inr hu)
  have u2 : p121 := by
    rcases h21670 with q0 | q1 | q2
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact q2
  rcases h31813 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)

theorem step35228 (p2 p192 p424 p790 : Prop)
    (h27760 : (¬ p2) ∨ (¬ p790) ∨ p192)
    (h27876 : (¬ p2) ∨ (¬ p192) ∨ (¬ p424)) : (¬ p2) ∨ (¬ p790) ∨ (¬ p424) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p192 := by
    rcases h27760 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact False.elim (q1 u1)
    · exact q2
  rcases h27876 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)

theorem step35229 (p3 p163 p185 p192 : Prop)
    (h33274 : p3 ∨ p185 ∨ p192)
    (h27363 : p3 ∨ (¬ p192) ∨ (¬ p163)) : p3 ∨ p185 ∨ (¬ p163) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p192 := by
    rcases h33274 with q0 | q1 | q2
    · exact False.elim (u0 q0)
    · exact False.elim (u1 q1)
    · exact q2
  rcases h27363 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)

theorem step35230 (p3 p101 p124 p207 : Prop)
    (h9049 : (¬ p101) ∨ (¬ p124) ∨ (¬ p207))
    (h25082 : p3 ∨ (¬ p124) ∨ p207) : (¬ p101) ∨ (¬ p124) ∨ p3 := by
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
  have u2 : (¬ p3) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : (¬ p207) := by
    rcases h9049 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact False.elim (q1 u1)
    · exact q2
  rcases h25082 with q0 | q1 | q2
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (u3 q2)

theorem step35240 (p1 p225 p540 : Prop)
    (h21590 : p1 ∨ p540 ∨ p225)
    (h32369 : p540 ∨ (¬ p225) ∨ p1) : p1 ∨ p540 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p540) := fun hu => hn (Or.inr hu)
  have u2 : p225 := by
    rcases h21590 with q0 | q1 | q2
    · exact False.elim (u0 q0)
    · exact False.elim (u1 q1)
    · exact q2
  rcases h32369 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (u0 q2)

theorem step35370 (p12 p1037 p1041 p1053 : Prop)
    (h24759 : (¬ p1053) ∨ p1037 ∨ p12)
    (h24754 : p1053 ∨ p1037 ∨ p1041) : p1037 ∨ p12 ∨ p1041 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1037) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1041) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1053) := by
    rcases h24759 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h24754 with q0 | q1 | q2
  · exact False.elim (u3 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (u2 q2)

theorem step35410 (p1385 p1389 p1392 p1405 : Prop)
    (h34689 : p1389 ∨ (¬ p1405) ∨ (¬ p1385))
    (h26327 : p1405 ∨ p1389 ∨ p1392) : p1389 ∨ (¬ p1385) ∨ p1392 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1389) := fun hu => hn (Or.inl hu)
  have u1 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1392) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1405) := by
    rcases h34689 with q0 | q1 | q2
    · exact False.elim (u0 q0)
    · exact q1
    · exact False.elim (q2 u1)
  rcases h26327 with q0 | q1 | q2
  · exact False.elim (u3 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (u2 q2)

theorem step35495 (p39 p41 : Prop)
    (h25573 : p39 ∨ p41)
    (h21001 : p39 ∨ (¬ p41)) : p39 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p39) := fun hu => hn hu
  have u1 : p41 := by
    rcases h25573 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h21001 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)

theorem step35496 (p63 p86 : Prop)
    (h21852 : p86 ∨ p63)
    (h21017 : (¬ p63) ∨ p86) : p86 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p86) := fun hu => hn hu
  have u1 : p63 := by
    rcases h21852 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h21017 with q0 | q1
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)

theorem step35497 (p63 p87 : Prop)
    (h23714 : p87 ∨ p63)
    (h21021 : (¬ p63) ∨ p87) : p87 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p87) := fun hu => hn hu
  have u1 : p63 := by
    rcases h23714 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h21021 with q0 | q1
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)

theorem step35498 (p185 p244 : Prop)
    (h34415 : p244 ∨ p185)
    (h19754 : (¬ p185) ∨ p244) : p244 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p244) := fun hu => hn hu
  have u1 : p185 := by
    rcases h34415 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h19754 with q0 | q1
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)

theorem step35499 (p18 p330 : Prop)
    (h25605 : p330 ∨ (¬ p18))
    (h27668 : p18 ∨ p330) : p330 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p330) := fun hu => hn hu
  have u1 : (¬ p18) := by
    rcases h25605 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h27668 with q0 | q1
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)

theorem step35500 (p495 p496 : Prop)
    (h33825 : p496 ∨ (¬ p495))
    (h27090 : p496 ∨ p495) : p496 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p496) := fun hu => hn hu
  have u1 : (¬ p495) := by
    rcases h33825 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h27090 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)

theorem step35501 (p533 p980 : Prop)
    (h33824 : p533 ∨ (¬ p980))
    (h32999 : p533 ∨ p980) : p533 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p533) := fun hu => hn hu
  have u1 : (¬ p980) := by
    rcases h33824 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h32999 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)

theorem step35502 (p224 p664 : Prop)
    (h32549 : p664 ∨ (¬ p224))
    (h27460 : p224 ∨ p664) : p664 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p664) := fun hu => hn hu
  have u1 : (¬ p224) := by
    rcases h32549 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h27460 with q0 | q1
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)

theorem step35503 (p980 p985 : Prop)
    (h25169 : p985 ∨ p980)
    (h16348 : (¬ p980) ∨ p985) : p985 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p985) := fun hu => hn hu
  have u1 : p980 := by
    rcases h25169 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h16348 with q0 | q1
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)

theorem step35504 (p1096 p1103 : Prop)
    (h33489 : p1103 ∨ (¬ p1096))
    (h28442 : p1096 ∨ p1103) : p1103 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1103) := fun hu => hn hu
  have u1 : (¬ p1096) := by
    rcases h33489 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h28442 with q0 | q1
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)

theorem step35505 (p1229 p1233 : Prop)
    (h16479 : (¬ p1229) ∨ p1233)
    (h21346 : p1233 ∨ p1229) : p1233 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1233) := fun hu => hn hu
  have u1 : (¬ p1229) := by
    rcases h16479 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h21346 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)

theorem step35506 (p38 p63 p67 : Prop)
    (h21299 : p67 ∨ p38)
    (h18227 : (¬ p38) ∨ (¬ p63) ∨ p67) : p67 ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p67) := fun hu => hn (Or.inl hu)
  have u1 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p38 := by
    rcases h21299 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h18227 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (u0 q2)

theorem step35507 (p3 p14 p38 p67 : Prop)
    (h27905 : p67 ∨ p14)
    (h21299 : p67 ∨ p38)
    (h28526 : p3 ∨ (¬ p14) ∨ (¬ p38)) : p67 ∨ p3 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p67) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr hu)
  have u2 : p14 := by
    rcases h27905 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p38 := by
    rcases h21299 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h28526 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)

theorem step35508 (p2 p38 p67 p234 : Prop)
    (h21299 : p67 ∨ p38)
    (h30461 : p67 ∨ p2)
    (h27759 : (¬ p38) ∨ (¬ p234) ∨ (¬ p2)) : p67 ∨ (¬ p234) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p67) := fun hu => hn (Or.inl hu)
  have u1 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p38 := by
    rcases h21299 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p2 := by
    rcases h30461 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h27759 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)

theorem step35509 (p2 p6 p67 p329 : Prop)
    (h24860 : p67 ∨ (¬ p6))
    (h30461 : p67 ∨ p2)
    (h13807 : (¬ p2) ∨ p6 ∨ (¬ p329)) : p67 ∨ (¬ p329) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p67) := fun hu => hn (Or.inl hu)
  have u1 : p329 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p6) := by
    rcases h24860 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p2 := by
    rcases h30461 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h13807 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)

theorem step35510 (p2 p6 p67 p101 : Prop)
    (h24860 : p67 ∨ (¬ p6))
    (h30461 : p67 ∨ p2)
    (h33564 : (¬ p2) ∨ p6 ∨ p101) : p67 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p67) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p101) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p6) := by
    rcases h24860 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p2 := by
    rcases h30461 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h33564 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (u2 q1)
  · exact False.elim (u1 q2)

theorem step35511 (p16 p63 p83 : Prop)
    (h25231 : p83 ∨ p63)
    (h31156 : p16 ∨ (¬ p83) ∨ p63) : p63 ∨ p16 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p63) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p16) := fun hu => hn (Or.inr hu)
  have u2 : p83 := by
    rcases h25231 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h31156 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (u0 q2)

theorem step35512 (p1 p2 p3 p67 : Prop)
    (h35507 : p67 ∨ p3)
    (h30461 : p67 ∨ p2)
    (h31786 : (¬ p3) ∨ (¬ p1) ∨ (¬ p2)) : p67 ∨ (¬ p1) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p67) := fun hu => hn (Or.inl hu)
  have u1 : p1 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p3 := by
    rcases h35507 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p2 := by
    rcases h30461 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h31786 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)

theorem step35513 (p2 p3 p67 p344 : Prop)
    (h35507 : p67 ∨ p3)
    (h30461 : p67 ∨ p2)
    (h34354 : (¬ p2) ∨ (¬ p3) ∨ (¬ p344)) : p67 ∨ (¬ p344) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p67) := fun hu => hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p3 := by
    rcases h35507 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p2 := by
    rcases h30461 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h34354 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)

theorem step35515 (p10 p325 p329 : Prop)
    (h21610 : p329 ∨ p10)
    (h31674 : p325 ∨ p329 ∨ (¬ p10)) : p329 ∨ p325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p329) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p325) := fun hu => hn (Or.inr hu)
  have u2 : p10 := by
    rcases h21610 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h31674 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)

theorem step35516 (p10 p326 p329 : Prop)
    (h21610 : p329 ∨ p10)
    (h34438 : p326 ∨ p329 ∨ (¬ p10)) : p329 ∨ p326 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p329) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p326) := fun hu => hn (Or.inr hu)
  have u2 : p10 := by
    rcases h21610 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h34438 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)

theorem step35517 (p2 p67 p101 p124 p326 p329 : Prop)
    (h35510 : p67 ∨ p101)
    (h30461 : p67 ∨ p2)
    (h35509 : p67 ∨ (¬ p329))
    (h35516 : p329 ∨ p326)
    (h23964 : (¬ p101) ∨ (¬ p124) ∨ (¬ p326) ∨ (¬ p2)) : p67 ∨ (¬ p124) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p67) := fun hu => hn (Or.inl hu)
  have u1 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p101 := by
    rcases h35510 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p2 := by
    rcases h30461 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : (¬ p329) := by
    rcases h35509 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p326 := by
    rcases h35516 with q0 | q1
    · exact False.elim (u4 q0)
    · exact q1
  rcases h23964 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)

theorem step35521 (p6 p18 p25 p67 p124 p210 p234 p326 p329 p633 : Prop)
    (h35517 : p67 ∨ (¬ p124))
    (h24860 : p67 ∨ (¬ p6))
    (h25153 : p210 ∨ p6)
    (h35508 : p67 ∨ (¬ p234))
    (h19889 : (¬ p18) ∨ p67)
    (h23949 : p25 ∨ p18)
    (h35509 : p67 ∨ (¬ p329))
    (h35516 : p329 ∨ p326)
    (h32244 : p234 ∨ (¬ p210) ∨ (¬ p633) ∨ p124 ∨ (¬ p25) ∨ (¬ p326)) : p67 ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p67) := fun hu => hn (Or.inl hu)
  have u1 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p124) := by
    rcases h35517 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : (¬ p6) := by
    rcases h24860 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p210 := by
    rcases h25153 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u5 : (¬ p234) := by
    rcases h35508 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : (¬ p18) := by
    rcases h19889 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p25 := by
    rcases h23949 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : (¬ p329) := by
    rcases h35509 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u9 : p326 := by
    rcases h35516 with q0 | q1
    · exact False.elim (u8 q0)
    · exact q1
  rcases h32244 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (u2 q3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u9)

theorem step35523 (p67 p344 p633 p635 p897 : Prop)
    (h35521 : p67 ∨ (¬ p633))
    (h21505 : p633 ∨ p635)
    (h35513 : p67 ∨ (¬ p344))
    (h28109 : (¬ p635) ∨ p897 ∨ p344) : p67 ∨ p897 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p67) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p897) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p633) := by
    rcases h35521 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p635 := by
    rcases h21505 with q0 | q1
    · exact False.elim (u2 q0)
    · exact q1
  have u4 : (¬ p344) := by
    rcases h35513 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h28109 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (u1 q1)
  · exact False.elim (u4 q2)

theorem step35524 (p121 p134 p422 p1207 p1213 : Prop)
    (h16965 : (¬ p422) ∨ p1213)
    (h34074 : p1213 ∨ (¬ p121))
    (h21898 : p1207 ∨ p121)
    (h27656 : (¬ p1207) ∨ p422 ∨ (¬ p134)) : p1213 ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1213) := fun hu => hn (Or.inl hu)
  have u1 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p422) := by
    rcases h16965 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u3 : (¬ p121) := by
    rcases h34074 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1207 := by
    rcases h21898 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h27656 with q0 | q1 | q2
  · exact False.elim (q0 u4)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)

theorem step35525 (p330 p997 p1001 p1035 p1213 p1325 p1465 : Prop)
    (h35499 : p330)
    (h15332 : (¬ p330) ∨ (¬ p997) ∨ p1213)
    (h20681 : p997 ∨ p1001)
    (h19819 : (¬ p1035) ∨ p1213)
    (h21566 : p1465 ∨ p1035)
    (h27592 : (¬ p1001) ∨ p1325 ∨ (¬ p1465)) : p1213 ∨ p1325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1213) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr hu)
  have u2 : p330 := by
    exact h35499
  have u3 : (¬ p997) := by
    rcases h15332 with q0 | q1 | q2
    · exact False.elim (q0 u2)
    · exact q1
    · exact False.elim (u0 q2)
  have u4 : p1001 := by
    rcases h20681 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  have u5 : (¬ p1035) := by
    rcases h19819 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1465 := by
    rcases h21566 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h27592 with q0 | q1 | q2
  · exact False.elim (q0 u4)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u6)

theorem step35526 (p101 p121 p1080 p1083 : Prop)
    (h20936 : p1080 ∨ p1083)
    (h18529 : (¬ p121) ∨ p1080)
    (h27387 : (¬ p1083) ∨ p121 ∨ p101) : p1080 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1080) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p101) := fun hu => hn (Or.inr hu)
  have u2 : p1083 := by
    rcases h20936 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : (¬ p121) := by
    rcases h18529 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h27387 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (u3 q1)
  · exact False.elim (u1 q2)

theorem step35527 (p224 p662 p668 p836 p1115 : Prop)
    (h27494 : p668 ∨ p836)
    (h24673 : p224 ∨ p668)
    (h33291 : p662 ∨ (¬ p224))
    (h17267 : p668 ∨ (¬ p1115))
    (h12176 : (¬ p662) ∨ (¬ p836) ∨ p1115) : p668 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p668) := fun hu => hn hu
  have u1 : p836 := by
    rcases h27494 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u2 : p224 := by
    rcases h24673 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u3 : p662 := by
    rcases h33291 with q0 | q1
    · exact q0
    · exact False.elim (q1 u2)
  have u4 : (¬ p1115) := by
    rcases h17267 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h12176 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (u4 q2)

theorem step35528 (p635 p642 p1076 p1095 : Prop)
    (h28235 : p642 ∨ p1076)
    (h23006 : p642 ∨ p635)
    (h6476 : (¬ p635) ∨ (¬ p1076) ∨ (¬ p1095)) : p642 ∨ (¬ p1095) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p642) := fun hu => hn (Or.inl hu)
  have u1 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p1076 := by
    rcases h28235 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p635 := by
    rcases h23006 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6476 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)

theorem step35530 (p642 p1055 p1074 p1095 p1096 p1098 : Prop)
    (h35528 : p642 ∨ (¬ p1095))
    (h22311 : p1074 ∨ p1095)
    (h18091 : p642 ∨ (¬ p1096))
    (h21511 : p1098 ∨ p1096)
    (h28163 : (¬ p1098) ∨ (¬ p1074) ∨ p1055) : p642 ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p642) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p1095) := by
    rcases h35528 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p1074 := by
    rcases h22311 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : (¬ p1096) := by
    rcases h18091 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1098 := by
    rcases h21511 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h28163 with q0 | q1 | q2
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (u1 q2)

theorem step35531 (p15 p21 p25 p495 p583 : Prop)
    (h27091 : p495 ∨ p583)
    (h22748 : p583 ∨ (¬ p21))
    (h23917 : p21 ∨ p25)
    (h32265 : (¬ p495) ∨ (¬ p25) ∨ (¬ p15)) : p583 ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p583) := fun hu => hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p495 := by
    rcases h27091 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u3 : (¬ p21) := by
    rcases h22748 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p25 := by
    rcases h23917 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  rcases h32265 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)

theorem step35532 (p18 p21 p44 p134 p140 p583 : Prop)
    (h26196 : p583 ∨ (¬ p140))
    (h24119 : p140 ∨ p134)
    (h22748 : p583 ∨ (¬ p21))
    (h34009 : p21 ∨ (¬ p18))
    (h23796 : (¬ p44) ∨ p18 ∨ (¬ p134)) : p583 ∨ (¬ p44) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p583) := fun hu => hn (Or.inl hu)
  have u1 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p140) := by
    rcases h26196 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p134 := by
    rcases h24119 with q0 | q1
    · exact False.elim (u2 q0)
    · exact q1
  have u4 : (¬ p21) := by
    rcases h22748 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : (¬ p18) := by
    rcases h34009 with q0 | q1
    · exact False.elim (u4 q0)
    · exact q1
  rcases h23796 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u3)

theorem step35534 (p15 p44 p48 p63 p583 : Prop)
    (h35532 : p583 ∨ (¬ p44))
    (h21322 : p48 ∨ p44)
    (h35531 : p583 ∨ (¬ p15))
    (h28486 : (¬ p48) ∨ p15 ∨ (¬ p63)) : p583 ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p583) := fun hu => hn (Or.inl hu)
  have u1 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p44) := by
    rcases h35532 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p48 := by
    rcases h21322 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : (¬ p15) := by
    rcases h35531 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h28486 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u1)

theorem step35535 (p18 p21 p44 p48 p87 p134 p140 p189 p583 : Prop)
    (h35532 : p583 ∨ (¬ p44))
    (h21322 : p48 ∨ p44)
    (h22748 : p583 ∨ (¬ p21))
    (h34009 : p21 ∨ (¬ p18))
    (h35497 : p87)
    (h26196 : p583 ∨ (¬ p140))
    (h24119 : p140 ∨ p134)
    (h27695 : (¬ p189) ∨ p18 ∨ (¬ p134) ∨ (¬ p87) ∨ (¬ p48)) : p583 ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p583) := fun hu => hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p44) := by
    rcases h35532 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p48 := by
    rcases h21322 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : (¬ p21) := by
    rcases h22748 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : (¬ p18) := by
    rcases h34009 with q0 | q1
    · exact False.elim (u4 q0)
    · exact q1
  have u6 : p87 := by
    exact h35497
  have u7 : (¬ p140) := by
    rcases h26196 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u8 : p134 := by
    rcases h24119 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h27695 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)

theorem step35539 (p16 p63 : Prop)
    (h33622 : p16 ∨ (¬ p63))
    (h35511 : p63 ∨ p16) : p16 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p16) := fun hu => hn hu
  have u1 : (¬ p63) := by
    rcases h33622 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h35511 with q0 | q1
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)

theorem step35540 (p666 p980 p1325 p1330 : Prop)
    (h32035 : p980 ∨ p1330)
    (h27554 : p1330 ∨ (¬ p1325))
    (h29209 : (¬ p980) ∨ (¬ p666) ∨ p1325) : p1330 ∨ (¬ p666) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1330) := fun hu => hn (Or.inl hu)
  have u1 : p666 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p980 := by
    rcases h32035 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u3 : (¬ p1325) := by
    rcases h27554 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h29209 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (u3 q2)

theorem step35541 (p861 p1325 p1330 p1489 p1508 : Prop)
    (h17171 : p1330 ∨ (¬ p1508))
    (h21548 : p1508 ∨ p1489)
    (h27554 : p1330 ∨ (¬ p1325))
    (h28010 : (¬ p861) ∨ (¬ p1489) ∨ p1325) : p1330 ∨ (¬ p861) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1330) := fun hu => hn (Or.inl hu)
  have u1 : p861 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1508) := by
    rcases h17171 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p1489 := by
    rcases h21548 with q0 | q1
    · exact False.elim (u2 q0)
    · exact q1
  have u4 : (¬ p1325) := by
    rcases h27554 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h28010 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (u4 q2)

theorem step35543 (p101 p121 p1078 p1084 : Prop)
    (h31834 : p101 ∨ p1084)
    (h21635 : p1084 ∨ p1078)
    (h31818 : (¬ p1078) ∨ (¬ p121) ∨ (¬ p101)) : p1084 ∨ (¬ p121) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1084) := fun hu => hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p101 := by
    rcases h31834 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u3 : p1078 := by
    rcases h21635 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h31818 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)

theorem step35544 (p12 p101 p104 p1076 p1084 : Prop)
    (h31834 : p101 ∨ p1084)
    (h33371 : p104 ∨ (¬ p101))
    (h24284 : p1084 ∨ p1076)
    (h29302 : (¬ p104) ∨ (¬ p12) ∨ (¬ p1076)) : p1084 ∨ (¬ p12) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1084) := fun hu => hn (Or.inl hu)
  have u1 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p101 := by
    rcases h31834 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u3 : p104 := by
    rcases h33371 with q0 | q1
    · exact q0
    · exact False.elim (q1 u2)
  have u4 : p1076 := by
    rcases h24284 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h29302 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)

theorem step35547 (p224 p665 p734 p1325 p1332 : Prop)
    (h33292 : p665 ∨ (¬ p224))
    (h16960 : p665 ∨ (¬ p1325))
    (h24736 : p1332 ∨ p1325)
    (h10844 : p224 ∨ (¬ p734) ∨ (¬ p1332)) : p665 ∨ (¬ p734) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p665) := fun hu => hn (Or.inl hu)
  have u1 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p224) := by
    rcases h33292 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : (¬ p1325) := by
    rcases h16960 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1332 := by
    rcases h24736 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h10844 with q0 | q1 | q2
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)

theorem step35548 (p224 p665 p666 p980 p1325 : Prop)
    (h33292 : p665 ∨ (¬ p224))
    (h22413 : p666 ∨ p224)
    (h16960 : p665 ∨ (¬ p1325))
    (h29209 : (¬ p980) ∨ (¬ p666) ∨ p1325) : p665 ∨ (¬ p980) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p665) := fun hu => hn (Or.inl hu)
  have u1 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p224) := by
    rcases h33292 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p666 := by
    rcases h22413 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : (¬ p1325) := by
    rcases h16960 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h29209 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (u4 q2)

theorem step35549 (p303 p327 p328 p419 : Prop)
    (h29757 : p327 ∨ p419)
    (h22444 : p327 ∨ p328)
    (h18602 : (¬ p303) ∨ p327)
    (h12936 : p303 ∨ (¬ p328) ∨ (¬ p419)) : p327 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p327) := fun hu => hn hu
  have u1 : p419 := by
    rcases h29757 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u2 : p328 := by
    rcases h22444 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : (¬ p303) := by
    rcases h18602 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h12936 with q0 | q1 | q2
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)

theorem step35553 (p16 p63 p83 p263 p495 p496 p498 p580 : Prop)
    (h35539 : p16)
    (h14850 : (¬ p16) ∨ p263 ∨ (¬ p498))
    (h24487 : p498 ∨ p495)
    (h35500 : p496)
    (h14244 : (¬ p83) ∨ p263 ∨ (¬ p496))
    (h25231 : p83 ∨ p63)
    (h27087 : (¬ p580) ∨ (¬ p495) ∨ (¬ p63)) : p263 ∨ (¬ p580) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p263) := fun hu => hn (Or.inl hu)
  have u1 : p580 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p16 := by
    exact h35539
  have u3 : (¬ p498) := by
    rcases h14850 with q0 | q1 | q2
    · exact False.elim (q0 u2)
    · exact False.elim (u0 q1)
    · exact q2
  have u4 : p495 := by
    rcases h24487 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  have u5 : p496 := by
    exact h35500
  have u6 : (¬ p83) := by
    rcases h14244 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u5)
  have u7 : p63 := by
    rcases h25231 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h27087 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u7)

theorem step35554 (p16 p63 p83 p88 p263 p421 p495 p496 p498 p576 p577 p580 : Prop)
    (h35539 : p16)
    (h14850 : (¬ p16) ∨ p263 ∨ (¬ p498))
    (h24487 : p498 ∨ p495)
    (h27236 : p421 ∨ (¬ p495))
    (h35553 : p263 ∨ (¬ p580))
    (h21165 : p576 ∨ p580)
    (h33822 : p577 ∨ (¬ p576))
    (h35500 : p496)
    (h14244 : (¬ p83) ∨ p263 ∨ (¬ p496))
    (h25231 : p83 ∨ p63)
    (h33621 : p88 ∨ (¬ p63))
    (h13289 : (¬ p88) ∨ p263 ∨ (¬ p421) ∨ (¬ p577)) : p263 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p263) := fun hu => hn hu
  have u1 : p16 := by
    exact h35539
  have u2 : (¬ p498) := by
    rcases h14850 with q0 | q1 | q2
    · exact False.elim (q0 u1)
    · exact False.elim (u0 q1)
    · exact q2
  have u3 : p495 := by
    rcases h24487 with q0 | q1
    · exact False.elim (u2 q0)
    · exact q1
  have u4 : p421 := by
    rcases h27236 with q0 | q1
    · exact q0
    · exact False.elim (q1 u3)
  have u5 : (¬ p580) := by
    rcases h35553 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p576 := by
    rcases h21165 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u7 : p577 := by
    rcases h33822 with q0 | q1
    · exact q0
    · exact False.elim (q1 u6)
  have u8 : p496 := by
    exact h35500
  have u9 : (¬ p83) := by
    rcases h14244 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u8)
  have u10 : p63 := by
    rcases h25231 with q0 | q1
    · exact False.elim (u9 q0)
    · exact q1
  have u11 : p88 := by
    rcases h33621 with q0 | q1
    · exact q0
    · exact False.elim (q1 u10)
  rcases h13289 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u11)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u7)

theorem step35555 (p6 p209 p210 : Prop)
    (h25153 : p210 ∨ p6)
    (h34612 : p209 ∨ p210 ∨ (¬ p6)) : p210 ∨ p209 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p210) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p209) := fun hu => hn (Or.inr hu)
  have u2 : p6 := by
    rcases h25153 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h34612 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)

theorem step35556 (p6 p134 p187 p195 : Prop)
    (h19412 : (¬ p6) ∨ p195)
    (h28553 : p134 ∨ p195)
    (h25120 : p195 ∨ p187)
    (h32313 : (¬ p187) ∨ (¬ p134) ∨ p6) : p195 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p195) := fun hu => hn hu
  have u1 : (¬ p6) := by
    rcases h19412 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u2 : p134 := by
    rcases h28553 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u3 : p187 := by
    rcases h25120 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h32313 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)

theorem step35557 (p134 p135 p136 : Prop)
    (h33333 : p136 ∨ (¬ p134))
    (h24376 : p134 ∨ p136 ∨ p135) : p136 ∨ p135 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p136) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p135) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p134) := by
    rcases h33333 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h24376 with q0 | q1 | q2
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)

theorem step35558 (p5 p15 p68 : Prop)
    (h21595 : p68 ∨ p15)
    (h33519 : p5 ∨ p68 ∨ (¬ p15)) : p68 ∨ p5 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p68) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p5) := fun hu => hn (Or.inr hu)
  have u2 : p15 := by
    rcases h21595 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h33519 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)

theorem step35559 (p15 p68 p72 : Prop)
    (h21595 : p68 ∨ p15)
    (h34363 : p72 ∨ p68 ∨ (¬ p15)) : p68 ∨ p72 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p68) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p72) := fun hu => hn (Or.inr hu)
  have u2 : p15 := by
    rcases h21595 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h34363 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)

theorem step35560 (p15 p44 p50 p89 p189 : Prop)
    (h22877 : p50 ∨ p44)
    (h17102 : p50 ∨ (¬ p189))
    (h17354 : (¬ p15) ∨ p50)
    (h27751 : (¬ p44) ∨ p189 ∨ (¬ p89) ∨ p15) : p50 ∨ (¬ p89) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p50) := fun hu => hn (Or.inl hu)
  have u1 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p44 := by
    rcases h22877 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : (¬ p189) := by
    rcases h17102 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : (¬ p15) := by
    rcases h17354 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h27751 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (u4 q3)

theorem step35563 (p1385 p1389 p1392 : Prop)
    (h24585 : p1392 ∨ p1385)
    (h35410 : p1389 ∨ (¬ p1385) ∨ p1392) : p1392 ∨ p1389 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1392) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1389) := fun hu => hn (Or.inr hu)
  have u2 : p1385 := by
    rcases h24585 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h35410 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (u0 q2)

theorem step35564 (p1385 p1388 p1395 : Prop)
    (h34197 : p1388 ∨ (¬ p1385))
    (h20821 : p1395 ∨ p1388 ∨ p1385) : p1388 ∨ p1395 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1388) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1395) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p1385) := by
    rcases h34197 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h20821 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (u2 q2)

theorem step35565 (p663 p980 p1325 p1335 : Prop)
    (h21904 : p1335 ∨ p1325)
    (h17334 : (¬ p980) ∨ p1335)
    (h33000 : p980 ∨ (¬ p663) ∨ (¬ p1325)) : p1335 ∨ (¬ p663) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1335) := fun hu => hn (Or.inl hu)
  have u1 : p663 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p1325 := by
    rcases h21904 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : (¬ p980) := by
    rcases h17334 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h33000 with q0 | q1 | q2
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)

theorem step35566 (p980 p1287 p1325 p1335 : Prop)
    (h21904 : p1335 ∨ p1325)
    (h17334 : (¬ p980) ∨ p1335)
    (h34047 : p980 ∨ (¬ p1287) ∨ (¬ p1325)) : p1335 ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1335) := fun hu => hn (Or.inl hu)
  have u1 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p1325 := by
    rcases h21904 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : (¬ p980) := by
    rcases h17334 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h34047 with q0 | q1 | q2
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)

theorem step35568 (p419 p435 p1000 p1325 p1332 : Prop)
    (h34848 : p1000 ∨ (¬ p419))
    (h17351 : p1000 ∨ (¬ p1325))
    (h24736 : p1332 ∨ p1325)
    (h29758 : p419 ∨ (¬ p1332) ∨ (¬ p435)) : p1000 ∨ (¬ p435) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1000) := fun hu => hn (Or.inl hu)
  have u1 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p419) := by
    rcases h34848 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : (¬ p1325) := by
    rcases h17351 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1332 := by
    rcases h24736 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h29758 with q0 | q1 | q2
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)

theorem step35569 (p419 p1000 p1001 p1325 p1465 : Prop)
    (h34848 : p1000 ∨ (¬ p419))
    (h24418 : p1001 ∨ p419)
    (h17351 : p1000 ∨ (¬ p1325))
    (h27592 : (¬ p1001) ∨ p1325 ∨ (¬ p1465)) : p1000 ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1000) := fun hu => hn (Or.inl hu)
  have u1 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p419) := by
    rcases h34848 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p1001 := by
    rcases h24418 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : (¬ p1325) := by
    rcases h17351 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h27592 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u1)

theorem step35571 (p633 p638 p639 p1074 p1076 : Prop)
    (h25376 : p633 ∨ p638)
    (h34085 : p639 ∨ (¬ p633))
    (h18906 : p638 ∨ (¬ p1076))
    (h28220 : p1076 ∨ (¬ p639) ∨ (¬ p1074)) : p638 ∨ (¬ p1074) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p638) := fun hu => hn (Or.inl hu)
  have u1 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p633 := by
    rcases h25376 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u3 : p639 := by
    rcases h34085 with q0 | q1
    · exact q0
    · exact False.elim (q1 u2)
  have u4 : (¬ p1076) := by
    rcases h18906 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h28220 with q0 | q1 | q2
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)

theorem step35572 (p420 p596 p599 : Prop)
    (h22572 : p596 ∨ p420)
    (h33442 : p599 ∨ p596 ∨ (¬ p420)) : p596 ∨ p599 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p596) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p599) := fun hu => hn (Or.inr hu)
  have u2 : p420 := by
    rcases h22572 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h33442 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)

theorem step35573 (p495 p575 p576 p582 p1233 : Prop)
    (h24411 : p582 ∨ p576)
    (h33823 : p575 ∨ (¬ p576))
    (h35505 : p1233)
    (h19876 : (¬ p495) ∨ (¬ p575) ∨ p582 ∨ (¬ p1233)) : p582 ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p582) := fun hu => hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p576 := by
    rcases h24411 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p575 := by
    rcases h33823 with q0 | q1
    · exact q0
    · exact False.elim (q1 u2)
  have u4 : p1233 := by
    exact h35505
  rcases h19876 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u4)

theorem step35574 (p63 p495 p575 p576 p582 : Prop)
    (h35573 : p582 ∨ (¬ p495))
    (h17749 : (¬ p63) ∨ p582)
    (h24411 : p582 ∨ p576)
    (h33823 : p575 ∨ (¬ p576))
    (h30233 : p495 ∨ p63 ∨ (¬ p575)) : p582 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p582) := fun hu => hn hu
  have u1 : (¬ p495) := by
    rcases h35573 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u2 : (¬ p63) := by
    rcases h17749 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u3 : p576 := by
    rcases h24411 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p575 := by
    rcases h33823 with q0 | q1
    · exact q0
    · exact False.elim (q1 u3)
  rcases h30233 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)

theorem step35575 (p21 p25 p39 p101 p577 : Prop)
    (h35495 : p39)
    (h14387 : (¬ p25) ∨ (¬ p39) ∨ p577)
    (h23917 : p21 ∨ p25)
    (h18466 : (¬ p21) ∨ (¬ p101) ∨ p577) : p577 ∨ (¬ p101) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p577) := fun hu => hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p39 := by
    exact h35495
  have u3 : (¬ p25) := by
    rcases h14387 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u2)
    · exact False.elim (u0 q2)
  have u4 : p21 := by
    rcases h23917 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18466 with q0 | q1 | q2
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (u0 q2)

theorem step35576 (p18 p25 p39 p41 p576 p577 : Prop)
    (h35495 : p39)
    (h14387 : (¬ p25) ∨ (¬ p39) ∨ p577)
    (h23949 : p25 ∨ p18)
    (h33822 : p577 ∨ (¬ p576))
    (h33303 : p576 ∨ (¬ p18) ∨ p41) : p577 ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p577) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p41) := fun hu => hn (Or.inr hu)
  have u2 : p39 := by
    exact h35495
  have u3 : (¬ p25) := by
    rcases h14387 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u2)
    · exact False.elim (u0 q2)
  have u4 : p18 := by
    rcases h23949 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  have u5 : (¬ p576) := by
    rcases h33822 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h33303 with q0 | q1 | q2
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)

theorem step35577 (p18 p25 p39 p41 p47 p134 p577 : Prop)
    (h35576 : p577 ∨ p41)
    (h33305 : (¬ p41) ∨ p47)
    (h35495 : p39)
    (h14387 : (¬ p25) ∨ (¬ p39) ∨ p577)
    (h23949 : p25 ∨ p18)
    (h28651 : (¬ p18) ∨ (¬ p47) ∨ p134) : p577 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p577) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p134) := fun hu => hn (Or.inr hu)
  have u2 : p41 := by
    rcases h35576 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p47 := by
    rcases h33305 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u4 : p39 := by
    exact h35495
  have u5 : (¬ p25) := by
    rcases h14387 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u4)
    · exact False.elim (u0 q2)
  have u6 : p18 := by
    rcases h23949 with q0 | q1
    · exact False.elim (u5 q0)
    · exact q1
  rcases h28651 with q0 | q1 | q2
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u3)
  · exact False.elim (u1 q2)

theorem step35579 (p2 p3 p225 p539 p563 : Prop)
    (h33985 : p563 ∨ (¬ p3))
    (h28906 : p225 ∨ p563)
    (h33767 : p539 ∨ (¬ p225))
    (h27615 : p3 ∨ (¬ p539) ∨ p2) : p563 ∨ p2 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p563) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p2) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p3) := by
    rcases h33985 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p225 := by
    rcases h28906 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p539 := by
    rcases h33767 with q0 | q1
    · exact q0
    · exact False.elim (q1 u3)
  rcases h27615 with q0 | q1 | q2
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)

theorem step35581 (p3 p8 p225 p557 p563 : Prop)
    (h33985 : p563 ∨ (¬ p3))
    (h21089 : p3 ∨ p557)
    (h28906 : p225 ∨ p563)
    (h29061 : (¬ p557) ∨ (¬ p8) ∨ (¬ p225)) : p563 ∨ (¬ p8) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p563) := fun hu => hn (Or.inl hu)
  have u1 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p3) := by
    rcases h33985 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p557 := by
    rcases h21089 with q0 | q1
    · exact False.elim (u2 q0)
    · exact q1
  have u4 : p225 := by
    rcases h28906 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h29061 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)

theorem step35582 (p225 p542 p543 : Prop)
    (h23630 : p543 ∨ p225)
    (h34083 : p542 ∨ p543 ∨ (¬ p225)) : p543 ∨ p542 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p543) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p542) := fun hu => hn (Or.inr hu)
  have u2 : p225 := by
    rcases h23630 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h34083 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)

theorem step35585 (p125 p366 p367 : Prop)
    (h21948 : p367 ∨ p125)
    (h32888 : p366 ∨ p367 ∨ (¬ p125)) : p367 ∨ p366 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p367) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p366) := fun hu => hn (Or.inr hu)
  have u2 : p125 := by
    rcases h21948 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h32888 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)

theorem step35586 (p8 p306 p344 p351 : Prop)
    (h34428 : p351 ∨ (¬ p344))
    (h32947 : p351 ∨ p8)
    (h29056 : (¬ p306) ∨ (¬ p8) ∨ p344) : p351 ∨ (¬ p306) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p351) := fun hu => hn (Or.inl hu)
  have u1 : p306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p344) := by
    rcases h34428 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p8 := by
    rcases h32947 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h29056 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (u2 q2)

theorem step35587 (p4 p8 p124 p125 p306 p310 p344 p351 : Prop)
    (h34428 : p351 ∨ (¬ p344))
    (h22566 : p4 ∨ p344)
    (h32947 : p351 ∨ p8)
    (h35586 : p351 ∨ (¬ p306))
    (h24995 : p306 ∨ p124)
    (h28857 : p310 ∨ (¬ p124))
    (h28877 : (¬ p125) ∨ (¬ p8) ∨ (¬ p4) ∨ (¬ p310)) : p351 ∨ (¬ p125) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p351) := fun hu => hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p344) := by
    rcases h34428 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p4 := by
    rcases h22566 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : p8 := by
    rcases h32947 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : (¬ p306) := by
    rcases h35586 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p124 := by
    rcases h24995 with q0 | q1
    · exact False.elim (u5 q0)
    · exact q1
  have u7 : p310 := by
    rcases h28857 with q0 | q1
    · exact q0
    · exact False.elim (q1 u6)
  rcases h28877 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u7)

theorem step35589 (p15 p326 p329 : Prop)
    (h35516 : p329 ∨ p326)
    (h16535 : (¬ p15) ∨ p326 ∨ (¬ p329)) : p326 ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p326) := fun hu => hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p329 := by
    rcases h35516 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h16535 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)

theorem step35590 (p18 p234 p326 p329 : Prop)
    (h35516 : p329 ∨ p326)
    (h20241 : (¬ p234) ∨ p326)
    (h27672 : p234 ∨ p18 ∨ (¬ p329)) : p326 ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p326) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p18) := fun hu => hn (Or.inr hu)
  have u2 : p329 := by
    rcases h35516 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u3 : (¬ p234) := by
    rcases h20241 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h27672 with q0 | q1 | q2
  · exact False.elim (u3 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)

theorem step35591 (p15 p18 p326 p1096 : Prop)
    (h35589 : p326 ∨ (¬ p15))
    (h35590 : p326 ∨ p18)
    (h34101 : p15 ∨ (¬ p18) ∨ (¬ p1096)) : p326 ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p326) := fun hu => hn (Or.inl hu)
  have u1 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p15) := by
    rcases h35589 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p18 := by
    rcases h35590 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h34101 with q0 | q1 | q2
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)

theorem step35592 (p2 p15 p234 p326 : Prop)
    (h35589 : p326 ∨ (¬ p15))
    (h20241 : (¬ p234) ∨ p326)
    (h30486 : p234 ∨ p15 ∨ p2) : p326 ∨ p2 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p326) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p2) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p15) := by
    rcases h35589 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : (¬ p234) := by
    rcases h20241 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h30486 with q0 | q1 | q2
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (u1 q2)

theorem step35594 (p6 p15 p18 p68 p326 : Prop)
    (h35589 : p326 ∨ (¬ p15))
    (h21595 : p68 ∨ p15)
    (h35590 : p326 ∨ p18)
    (h33161 : p6 ∨ (¬ p18) ∨ (¬ p68)) : p326 ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p326) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p15) := by
    rcases h35589 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p68 := by
    rcases h21595 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : p18 := by
    rcases h35590 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h33161 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)

theorem step35595 (p15 p18 p20 p326 p495 : Prop)
    (h35590 : p326 ∨ p18)
    (h33849 : p20 ∨ (¬ p18))
    (h35589 : p326 ∨ (¬ p15))
    (h31268 : p495 ∨ p15 ∨ (¬ p20)) : p326 ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p326) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr hu)
  have u2 : p18 := by
    rcases h35590 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p20 := by
    rcases h33849 with q0 | q1
    · exact q0
    · exact False.elim (q1 u2)
  have u4 : (¬ p15) := by
    rcases h35589 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h31268 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u3)

theorem step35596 (p63 p124 p308 p309 : Prop)
    (h25081 : p124 ∨ p308)
    (h33283 : p309 ∨ (¬ p124))
    (h30766 : p308 ∨ p63 ∨ (¬ p309)) : p308 ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p308) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p63) := fun hu => hn (Or.inr hu)
  have u2 : p124 := by
    rcases h25081 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u3 : p309 := by
    rcases h33283 with q0 | q1
    · exact q0
    · exact False.elim (q1 u2)
  rcases h30766 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)

theorem step35597 (p124 p308 p309 p1055 p1076 : Prop)
    (h29068 : p308 ∨ p1055)
    (h25081 : p124 ∨ p308)
    (h33283 : p309 ∨ (¬ p124))
    (h30764 : p1076 ∨ (¬ p309) ∨ (¬ p1055)) : p308 ∨ p1076 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p308) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr hu)
  have u2 : p1055 := by
    rcases h29068 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p124 := by
    rcases h25081 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p309 := by
    rcases h33283 with q0 | q1
    · exact q0
    · exact False.elim (q1 u3)
  rcases h30764 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)

theorem step35599 (p17 p137 p207 p262 p268 : Prop)
    (h24278 : p268 ∨ p17)
    (h33328 : p262 ∨ (¬ p17))
    (h22794 : p268 ∨ (¬ p207))
    (h13495 : (¬ p137) ∨ p207 ∨ (¬ p262)) : p268 ∨ (¬ p137) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p268) := fun hu => hn (Or.inl hu)
  have u1 : p137 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p17 := by
    rcases h24278 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p262 := by
    rcases h33328 with q0 | q1
    · exact q0
    · exact False.elim (q1 u2)
  have u4 : (¬ p207) := by
    rcases h22794 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h13495 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u3)

theorem step35600 (p134 p137 p143 : Prop)
    (h33357 : (¬ p134) ∨ p137)
    (h24289 : p143 ∨ p134 ∨ p137) : p137 ∨ p143 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p137) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p143) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p134) := by
    rcases h33357 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h24289 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (u0 q2)

theorem step35601 (p17 p134 p137 p141 p189 p268 : Prop)
    (h35599 : p268 ∨ (¬ p137))
    (h33357 : (¬ p134) ∨ p137)
    (h24112 : p141 ∨ p134)
    (h24278 : p268 ∨ p17)
    (h14990 : (¬ p17) ∨ (¬ p141) ∨ p189) : p268 ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p268) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p137) := by
    rcases h35599 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : (¬ p134) := by
    rcases h33357 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : p141 := by
    rcases h24112 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u5 : p17 := by
    rcases h24278 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h14990 with q0 | q1 | q2
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)

theorem step35602 (p8 p240 p241 p836 : Prop)
    (h23536 : p240 ∨ p241)
    (h17081 : (¬ p8) ∨ p240)
    (h30871 : (¬ p241) ∨ p8 ∨ p836) : p240 ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p240) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p836) := fun hu => hn (Or.inr hu)
  have u2 : p241 := by
    rcases h23536 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : (¬ p8) := by
    rcases h17081 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h30871 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (u3 q1)
  · exact False.elim (u1 q2)

theorem step35604 (p9 p16 p89 p239 p242 : Prop)
    (h35539 : p16)
    (h15324 : (¬ p9) ∨ (¬ p16) ∨ p239)
    (h24753 : p239 ∨ p242)
    (h16145 : p9 ∨ (¬ p89) ∨ (¬ p242)) : p239 ∨ (¬ p89) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p239) := fun hu => hn (Or.inl hu)
  have u1 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p16 := by
    exact h35539
  have u3 : (¬ p9) := by
    rcases h15324 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u2)
    · exact False.elim (u0 q2)
  have u4 : p242 := by
    rcases h24753 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h16145 with q0 | q1 | q2
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)

theorem step35606 (p15 p228 p383 : Prop)
    (h21206 : p383 ∨ p228)
    (h19366 : (¬ p15) ∨ p228 ∨ (¬ p383)) : p228 ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p228) := fun hu => hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p383 := by
    rcases h21206 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19366 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)

theorem step35607 (p121 p209 p210 p227 p961 : Prop)
    (h17910 : p209 ∨ (¬ p227))
    (h21044 : p961 ∨ p227)
    (h35555 : p210 ∨ p209)
    (h11127 : (¬ p121) ∨ (¬ p210) ∨ (¬ p961)) : p209 ∨ (¬ p121) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p209) := fun hu => hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p227) := by
    rcases h17910 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p961 := by
    rcases h21044 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : p210 := by
    rcases h35555 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h11127 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)

theorem step35609 (p121 p134 p209 p422 p1207 : Prop)
    (h35607 : p209 ∨ (¬ p121))
    (h21898 : p1207 ∨ p121)
    (h28552 : p134 ∨ p209)
    (h27656 : (¬ p1207) ∨ p422 ∨ (¬ p134)) : p209 ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p209) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p422) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p121) := by
    rcases h35607 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p1207 := by
    rcases h21898 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : p134 := by
    rcases h28552 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h27656 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)

theorem step35611 (p163 p168 p169 : Prop)
    (h33527 : p169 ∨ (¬ p163))
    (h23425 : p168 ∨ p169 ∨ p163) : p169 ∨ p168 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p169) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p168) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p163) := by
    rcases h33527 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h23425 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (u2 q2)

theorem step35612 (p17 p135 p136 p189 : Prop)
    (h35557 : p136 ∨ p135)
    (h31065 : p135 ∨ p189)
    (h27349 : p17 ∨ (¬ p189) ∨ (¬ p136)) : p135 ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p135) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr hu)
  have u2 : p136 := by
    rcases h35557 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u3 : p189 := by
    rcases h31065 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h27349 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)

theorem step35613 (p17 p135 p185 p258 p283 : Prop)
    (h35612 : p135 ∨ p17)
    (h31064 : p135 ∨ p258)
    (h33269 : p283 ∨ (¬ p258))
    (h28854 : (¬ p283) ∨ p185 ∨ (¬ p17)) : p135 ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p135) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr hu)
  have u2 : p17 := by
    rcases h35612 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p258 := by
    rcases h31064 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p283 := by
    rcases h33269 with q0 | q1
    · exact q0
    · exact False.elim (q1 u3)
  rcases h28854 with q0 | q1 | q2
  · exact False.elim (q0 u4)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)

theorem step35614 (p17 p124 p135 p258 p262 : Prop)
    (h35612 : p135 ∨ p17)
    (h33328 : p262 ∨ (¬ p17))
    (h31064 : p135 ∨ p258)
    (h31883 : (¬ p258) ∨ (¬ p124) ∨ (¬ p262)) : p135 ∨ (¬ p124) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p135) := fun hu => hn (Or.inl hu)
  have u1 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p17 := by
    rcases h35612 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p262 := by
    rcases h33328 with q0 | q1
    · exact q0
    · exact False.elim (q1 u2)
  have u4 : p258 := by
    rcases h31064 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h31883 with q0 | q1 | q2
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)

theorem step35615 (p101 p105 p108 p189 : Prop)
    (h34380 : (¬ p101) ∨ p105)
    (h22658 : p108 ∨ p101)
    (h32350 : p105 ∨ p189 ∨ (¬ p108)) : p105 ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p105) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p101) := by
    rcases h34380 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u3 : p108 := by
    rcases h22658 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h32350 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)

theorem step35616 (p3 p6 p101 p105 p108 : Prop)
    (h17726 : (¬ p3) ∨ p105)
    (h34380 : (¬ p101) ∨ p105)
    (h22658 : p108 ∨ p101)
    (h27394 : p3 ∨ p6 ∨ (¬ p108)) : p105 ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p105) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p3) := by
    rcases h17726 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u3 : (¬ p101) := by
    rcases h34380 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p108 := by
    rcases h22658 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h27394 with q0 | q1 | q2
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)

theorem step35617 (p3 p105 p185 p188 p189 : Prop)
    (h17726 : (¬ p3) ∨ p105)
    (h35615 : p105 ∨ p189)
    (h33522 : p188 ∨ (¬ p189))
    (h27360 : p3 ∨ p185 ∨ (¬ p188) ∨ (¬ p189)) : p105 ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p105) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p3) := by
    rcases h17726 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u3 : p189 := by
    rcases h35615 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p188 := by
    rcases h33522 with q0 | q1
    · exact q0
    · exact False.elim (q1 u3)
  rcases h27360 with q0 | q1 | q2 | q3
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)

theorem step35620 (p6 p18 p68 p72 : Prop)
    (h35559 : p68 ∨ p72)
    (h19381 : (¬ p6) ∨ p72)
    (h33161 : p6 ∨ (¬ p18) ∨ (¬ p68)) : p72 ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p72) := fun hu => hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p68 := by
    rcases h35559 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u3 : (¬ p6) := by
    rcases h19381 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h33161 with q0 | q1 | q2
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)

theorem step35621 (p47 p68 p72 p192 p195 : Prop)
    (h35556 : p195)
    (h12171 : (¬ p47) ∨ p72 ∨ (¬ p195))
    (h35559 : p68 ∨ p72)
    (h15062 : p47 ∨ (¬ p68) ∨ (¬ p192)) : p72 ∨ (¬ p192) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p72) := fun hu => hn (Or.inl hu)
  have u1 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p195 := by
    exact h35556
  have u3 : (¬ p47) := by
    rcases h12171 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u2)
  have u4 : p68 := by
    rcases h35559 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h15062 with q0 | q1 | q2
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)

theorem step35627 (p6 p18 p23 p39 p63 : Prop)
    (h33847 : p23 ∨ (¬ p18))
    (h35495 : p39)
    (h33115 : p23 ∨ p6)
    (h34993 : p18 ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p6)) : p23 ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p23) := fun hu => hn (Or.inl hu)
  have u1 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p18) := by
    rcases h33847 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p39 := by
    exact h35495
  have u4 : p6 := by
    rcases h33115 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h34993 with q0 | q1 | q2 | q3
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)

theorem step35628 (p6 p18 p23 p38 : Prop)
    (h33847 : p23 ∨ (¬ p18))
    (h33115 : p23 ∨ p6)
    (h27721 : (¬ p38) ∨ p18 ∨ (¬ p6)) : p23 ∨ (¬ p38) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p23) := fun hu => hn (Or.inl hu)
  have u1 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p18) := by
    rcases h33847 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p6 := by
    rcases h33115 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h27721 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)

theorem step35630 (p6 p15 p18 p23 p24 p38 p64 p495 : Prop)
    (h35628 : p23 ∨ (¬ p38))
    (h33268 : (¬ p15) ∨ p38)
    (h21316 : p64 ∨ p15)
    (h33115 : p23 ∨ p6)
    (h33847 : p23 ∨ (¬ p18))
    (h24078 : p24 ∨ p18)
    (h27121 : (¬ p24) ∨ (¬ p64) ∨ (¬ p6) ∨ p495) : p23 ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p23) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p38) := by
    rcases h35628 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : (¬ p15) := by
    rcases h33268 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : p64 := by
    rcases h21316 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u5 : p6 := by
    rcases h33115 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : (¬ p18) := by
    rcases h33847 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p24 := by
    rcases h24078 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h27121 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (u1 q3)

theorem step35632 (p121 p1209 p1212 : Prop)
    (h31867 : p1212 ∨ (¬ p121))
    (h26556 : p1209 ∨ p1212 ∨ p121) : p1212 ∨ p1209 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1212) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1209) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p121) := by
    rcases h31867 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h26556 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (u2 q2)

theorem step35633 (p3 p12 p1044 : Prop)
    (h33345 : p1044 ∨ (¬ p12))
    (h33034 : p1044 ∨ p3 ∨ p12) : p1044 ∨ p3 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1044) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p12) := by
    rcases h33345 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h33034 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (u2 q2)

theorem step35634 (p12 p1040 p1041 : Prop)
    (h29300 : (¬ p12) ∨ p1041)
    (h26511 : p1040 ∨ p1041 ∨ p12) : p1041 ∨ p1040 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1041) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1040) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p12) := by
    rcases h29300 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h26511 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (u2 q2)

theorem step35635 (p12 p1037 p1041 : Prop)
    (h29300 : (¬ p12) ∨ p1041)
    (h35370 : p1037 ∨ p12 ∨ p1041) : p1041 ∨ p1037 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1041) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1037) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p12) := by
    rcases h29300 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h35370 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (u0 q2)

theorem step35636 (p918 p924 p927 : Prop)
    (h23359 : p927 ∨ p918)
    (h33813 : p924 ∨ p927 ∨ (¬ p918)) : p927 ∨ p924 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p927) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p924) := fun hu => hn (Or.inr hu)
  have u2 : p918 := by
    rcases h23359 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h33813 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)

theorem step35637 (p225 p542 p555 : Prop)
    (h28905 : p542 ∨ p225)
    (h34308 : p555 ∨ p542 ∨ (¬ p225)) : p542 ∨ p555 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p542) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p555) := fun hu => hn (Or.inr hu)
  have u2 : p225 := by
    rcases h28905 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h34308 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)

theorem step35638 (p126 p517 p518 : Prop)
    (h32007 : (¬ p126) ∨ p518)
    (h20901 : p517 ∨ p518 ∨ p126) : p518 ∨ p517 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p518) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p517) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p126) := by
    rcases h32007 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h20901 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (u2 q2)

theorem step35639 (p126 p515 p521 : Prop)
    (h25114 : p515 ∨ p126)
    (h33594 : p521 ∨ p515 ∨ (¬ p126)) : p515 ∨ p521 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p515) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p521) := fun hu => hn (Or.inr hu)
  have u2 : p126 := by
    rcases h25114 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h33594 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)

theorem step35640 (p344 p347 p360 : Prop)
    (h17118 : (¬ p344) ∨ p347)
    (h21053 : p360 ∨ p347 ∨ p344) : p347 ∨ p360 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p347) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p360) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p344) := by
    rcases h17118 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h21053 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (u2 q2)

theorem step35641 (p344 p347 p359 : Prop)
    (h17118 : (¬ p344) ∨ p347)
    (h21052 : p359 ∨ p347 ∨ p344) : p347 ∨ p359 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p347) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p359) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p344) := by
    rcases h17118 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h21052 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (u2 q2)

theorem step35642 (p344 p347 p358 : Prop)
    (h17118 : (¬ p344) ∨ p347)
    (h21051 : p358 ∨ p347 ∨ p344) : p347 ∨ p358 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p347) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p358) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p344) := by
    rcases h17118 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h21051 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (u2 q2)

theorem step35643 (p344 p347 p357 : Prop)
    (h17118 : (¬ p344) ∨ p347)
    (h21050 : p357 ∨ p347 ∨ p344) : p347 ∨ p357 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p347) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p357) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p344) := by
    rcases h17118 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h21050 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (u2 q2)

theorem step35644 (p344 p347 p357 p358 p359 p360 p361 : Prop)
    (h35643 : p347 ∨ p357)
    (h17118 : (¬ p344) ∨ p347)
    (h35640 : p347 ∨ p360)
    (h35642 : p347 ∨ p358)
    (h35641 : p347 ∨ p359)
    (h1872 : p344 ∨ p347 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361)) : p347 ∨ (¬ p361) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p347) := fun hu => hn (Or.inl hu)
  have u1 : p361 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p357 := by
    rcases h35643 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : (¬ p344) := by
    rcases h17118 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p360 := by
    rcases h35640 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p358 := by
    rcases h35642 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p359 := by
    rcases h35641 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1872 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u1)

theorem step35646 (p344 p347 p352 p353 p354 p355 p356 p361 : Prop)
    (h35644 : p347 ∨ (¬ p361))
    (h1934 : p353 ∨ p361)
    (h1929 : p352 ∨ p361)
    (h17118 : (¬ p344) ∨ p347)
    (h1949 : p356 ∨ p361)
    (h1944 : p355 ∨ p361)
    (h1939 : p354 ∨ p361)
    (h1847 : p344 ∨ p347 ∨ (¬ p352) ∨ (¬ p353) ∨ (¬ p354) ∨ (¬ p355) ∨ (¬ p356)) : p347 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p347) := fun hu => hn hu
  have u1 : (¬ p361) := by
    rcases h35644 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u2 : p353 := by
    rcases h1934 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u3 : p352 := by
    rcases h1929 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u4 : (¬ p344) := by
    rcases h17118 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p356 := by
    rcases h1949 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p355 := by
    rcases h1944 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p354 := by
    rcases h1939 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h1847 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u5)

theorem step35647 (p258 p283 p289 : Prop)
    (h33269 : p283 ∨ (¬ p258))
    (h21145 : p289 ∨ p283 ∨ p258) : p283 ∨ p289 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p283) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p289) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p258) := by
    rcases h33269 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h21145 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (u2 q2)

theorem step35648 (p255 p258 p290 : Prop)
    (h33270 : p255 ∨ (¬ p258))
    (h25762 : p290 ∨ p255 ∨ p258) : p255 ∨ p290 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p255) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p290) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p258) := by
    rcases h33270 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h25762 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (u2 q2)

theorem step35650 (p163 p166 p172 : Prop)
    (h25108 : p166 ∨ p163)
    (h34211 : p172 ∨ p166 ∨ (¬ p163)) : p166 ∨ p172 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p166) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p172) := fun hu => hn (Or.inr hu)
  have u2 : p163 := by
    rcases h25108 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h34211 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)

theorem step35651 (p156 p163 p180 : Prop)
    (h21005 : p156 ∨ (¬ p163))
    (h21999 : p180 ∨ p156 ∨ p163) : p156 ∨ p180 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p156) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p180) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p163) := by
    rcases h21005 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h21999 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (u2 q2)

theorem step35652 (p156 p163 p179 : Prop)
    (h21005 : p156 ∨ (¬ p163))
    (h22000 : p179 ∨ p156 ∨ p163) : p156 ∨ p179 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p156) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p179) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p163) := by
    rcases h21005 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h22000 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (u2 q2)

theorem step35653 (p156 p163 p182 : Prop)
    (h21005 : p156 ∨ (¬ p163))
    (h21998 : p182 ∨ p156 ∨ p163) : p156 ∨ p182 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p156) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p182) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p163) := by
    rcases h21005 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h21998 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (u2 q2)

theorem step35654 (p156 p163 p181 : Prop)
    (h21005 : p156 ∨ (¬ p163))
    (h21997 : p181 ∨ p156 ∨ p163) : p156 ∨ p181 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p156) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p181) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p163) := by
    rcases h21005 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h21997 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (u2 q2)

theorem step35655 (p156 p163 p178 p179 p180 p181 p182 : Prop)
    (h35654 : p156 ∨ p181)
    (h21005 : p156 ∨ (¬ p163))
    (h35651 : p156 ∨ p180)
    (h35653 : p156 ∨ p182)
    (h35652 : p156 ∨ p179)
    (h832 : p156 ∨ p163 ∨ (¬ p178) ∨ (¬ p179) ∨ (¬ p180) ∨ (¬ p181) ∨ (¬ p182)) : p156 ∨ (¬ p178) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p156) := fun hu => hn (Or.inl hu)
  have u1 : p178 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p181 := by
    rcases h35654 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : (¬ p163) := by
    rcases h21005 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p180 := by
    rcases h35651 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p182 := by
    rcases h35653 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p179 := by
    rcases h35652 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h832 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u5)

theorem step35659 (p156 p163 p173 p174 p175 p176 p177 p178 : Prop)
    (h35655 : p156 ∨ (¬ p178))
    (h890 : p173 ∨ p178)
    (h905 : p176 ∨ p178)
    (h21005 : p156 ∨ (¬ p163))
    (h895 : p174 ∨ p178)
    (h900 : p175 ∨ p178)
    (h910 : p177 ∨ p178)
    (h807 : p156 ∨ p163 ∨ (¬ p173) ∨ (¬ p174) ∨ (¬ p175) ∨ (¬ p176) ∨ (¬ p177)) : p156 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p156) := fun hu => hn hu
  have u1 : (¬ p178) := by
    rcases h35655 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u2 : p173 := by
    rcases h890 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u3 : p176 := by
    rcases h905 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u4 : (¬ p163) := by
    rcases h21005 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p174 := by
    rcases h895 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p175 := by
    rcases h900 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p177 := by
    rcases h910 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h807 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step35660 (p134 p138 p148 : Prop)
    (h28551 : p138 ∨ p134)
    (h33358 : p148 ∨ p138 ∨ (¬ p134)) : p138 ∨ p148 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p138) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p148) := fun hu => hn (Or.inr hu)
  have u2 : p134 := by
    rcases h28551 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h33358 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)

theorem step35661 (p134 p138 p153 : Prop)
    (h28551 : p138 ∨ p134)
    (h33448 : p153 ∨ p138 ∨ (¬ p134)) : p138 ∨ p153 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p138) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p153) := fun hu => hn (Or.inr hu)
  have u2 : p134 := by
    rcases h28551 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h33448 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)

theorem step35662 (p134 p138 p152 : Prop)
    (h28551 : p138 ∨ p134)
    (h33449 : p152 ∨ p138 ∨ (¬ p134)) : p138 ∨ p152 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p138) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p152) := fun hu => hn (Or.inr hu)
  have u2 : p134 := by
    rcases h28551 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h33449 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)

theorem step35663 (p134 p138 p151 : Prop)
    (h28551 : p138 ∨ p134)
    (h33450 : p151 ∨ p138 ∨ (¬ p134)) : p138 ∨ p151 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p138) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p151) := fun hu => hn (Or.inr hu)
  have u2 : p134 := by
    rcases h28551 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h33450 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)

theorem step35664 (p134 p138 p150 : Prop)
    (h28551 : p138 ∨ p134)
    (h33451 : p150 ∨ p138 ∨ (¬ p134)) : p138 ∨ p150 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p138) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p150) := fun hu => hn (Or.inr hu)
  have u2 : p134 := by
    rcases h28551 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h33451 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)

theorem step35665 (p134 p138 p149 p150 p151 p152 p153 : Prop)
    (h35662 : p138 ∨ p152)
    (h28551 : p138 ∨ p134)
    (h35661 : p138 ∨ p153)
    (h35664 : p138 ∨ p150)
    (h35663 : p138 ∨ p151)
    (h31017 : (¬ p149) ∨ p138 ∨ (¬ p134) ∨ (¬ p152) ∨ (¬ p153) ∨ (¬ p150) ∨ (¬ p151)) : p138 ∨ (¬ p149) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p138) := fun hu => hn (Or.inl hu)
  have u1 : p149 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p152 := by
    rcases h35662 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p134 := by
    rcases h28551 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p153 := by
    rcases h35661 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p150 := by
    rcases h35664 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p151 := by
    rcases h35663 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h31017 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)

theorem step35668 (p134 p138 p144 p145 p146 p147 p148 p149 : Prop)
    (h35665 : p138 ∨ (¬ p149))
    (h771 : p147 ∨ p149)
    (h756 : p144 ∨ p149)
    (h28551 : p138 ∨ p134)
    (h761 : p145 ∨ p149)
    (h766 : p146 ∨ p149)
    (h35660 : p138 ∨ p148)
    (h31019 : p138 ∨ (¬ p147) ∨ (¬ p134) ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p148)) : p138 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p138) := fun hu => hn hu
  have u1 : (¬ p149) := by
    rcases h35665 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u2 : p147 := by
    rcases h771 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u3 : p144 := by
    rcases h756 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u4 : p134 := by
    rcases h28551 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p145 := by
    rcases h761 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p146 := by
    rcases h766 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p148 := by
    rcases h35660 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h31019 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step35669 (p101 p106 p107 : Prop)
    (h24548 : p107 ∨ p101)
    (h34499 : p106 ∨ p107 ∨ (¬ p101)) : p107 ∨ p106 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p107) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p106) := fun hu => hn (Or.inr hu)
  have u2 : p101 := by
    rcases h24548 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h34499 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)

theorem step35675 (p331 p347 p348 p540 p545 : Prop)
    (h35646 : p347)
    (h13790 : p331 ∨ (¬ p347) ∨ (¬ p540))
    (h23351 : p545 ∨ p540)
    (h13739 : p331 ∨ (¬ p348) ∨ (¬ p545)) : p331 ∨ (¬ p348) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p331) := fun hu => hn (Or.inl hu)
  have u1 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p347 := by
    exact h35646
  have u3 : (¬ p540) := by
    rcases h13790 with q0 | q1 | q2
    · exact False.elim (u0 q0)
    · exact False.elim (q1 u2)
    · exact q2
  have u4 : p545 := by
    rcases h23351 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h13739 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)

theorem step35678 (p4 p325 p331 p347 p348 p540 : Prop)
    (h35675 : p331 ∨ (¬ p348))
    (h14189 : p4 ∨ p348)
    (h35646 : p347)
    (h13790 : p331 ∨ (¬ p347) ∨ (¬ p540))
    (h13133 : (¬ p4) ∨ (¬ p325) ∨ p540) : p331 ∨ (¬ p325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p331) := fun hu => hn (Or.inl hu)
  have u1 : p325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p348) := by
    rcases h35675 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p4 := by
    rcases h14189 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : p347 := by
    exact h35646
  have u5 : (¬ p540) := by
    rcases h13790 with q0 | q1 | q2
    · exact False.elim (u0 q0)
    · exact False.elim (q1 u4)
    · exact q2
  rcases h13133 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (u5 q2)

theorem step35679 (p104 p225 p331 p344 p347 p348 p540 : Prop)
    (h35675 : p331 ∨ (¬ p348))
    (h34013 : p348 ∨ (¬ p344))
    (h35646 : p347)
    (h13790 : p331 ∨ (¬ p347) ∨ (¬ p540))
    (h32370 : p540 ∨ (¬ p225))
    (h27790 : (¬ p104) ∨ p225 ∨ p344) : p331 ∨ (¬ p104) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p331) := fun hu => hn (Or.inl hu)
  have u1 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p348) := by
    rcases h35675 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : (¬ p344) := by
    rcases h34013 with q0 | q1
    · exact False.elim (u2 q0)
    · exact q1
  have u4 : p347 := by
    exact h35646
  have u5 : (¬ p540) := by
    rcases h13790 with q0 | q1 | q2
    · exact False.elim (u0 q0)
    · exact False.elim (q1 u4)
    · exact q2
  have u6 : (¬ p225) := by
    rcases h32370 with q0 | q1
    · exact False.elim (u5 q0)
    · exact q1
  rcases h27790 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (u6 q1)
  · exact False.elim (u3 q2)

theorem step35680 (p10 p325 p331 : Prop)
    (h35678 : p331 ∨ (¬ p325))
    (h22236 : p331 ∨ p325 ∨ p10) : p331 ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p331) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p10) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p325) := by
    rcases h35678 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h22236 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (u1 q2)

theorem step35686 (p4 p10 p104 p108 p225 p331 p347 p348 p540 : Prop)
    (h35680 : p331 ∨ p10)
    (h35679 : p331 ∨ (¬ p104))
    (h22239 : p108 ∨ p104)
    (h35675 : p331 ∨ (¬ p348))
    (h14189 : p4 ∨ p348)
    (h35646 : p347)
    (h13790 : p331 ∨ (¬ p347) ∨ (¬ p540))
    (h32370 : p540 ∨ (¬ p225))
    (h15053 : (¬ p4) ∨ (¬ p10) ∨ (¬ p108) ∨ p225) : p331 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p331) := fun hu => hn hu
  have u1 : p10 := by
    rcases h35680 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u2 : (¬ p104) := by
    rcases h35679 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p108 := by
    rcases h22239 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : (¬ p348) := by
    rcases h35675 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p4 := by
    rcases h14189 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u6 : p347 := by
    exact h35646
  have u7 : (¬ p540) := by
    rcases h13790 with q0 | q1 | q2
    · exact False.elim (u0 q0)
    · exact False.elim (q1 u6)
    · exact q2
  have u8 : (¬ p225) := by
    rcases h32370 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h15053 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (u8 q3)

theorem step35687 (p303 p515 p521 p789 : Prop)
    (h35639 : p515 ∨ p521)
    (h32681 : p521 ∨ p789)
    (h28340 : (¬ p515) ∨ (¬ p789) ∨ (¬ p303)) : p521 ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p521) := fun hu => hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p515 := by
    rcases h35639 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u3 : p789 := by
    rcases h32681 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h28340 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)

theorem step35688 (p12 p17 p41 p89 p225 p576 p1055 p1103 : Prop)
    (h35504 : p1103)
    (h26959 : (¬ p12) ∨ (¬ p41) ∨ (¬ p225) ∨ (¬ p1103) ∨ (¬ p1055) ∨ (¬ p576) ∨ (¬ p89) ∨ p17) : (¬ p89) ∨ (¬ p12) ∨ (¬ p225) ∨ (¬ p1055) ∨ (¬ p576) ∨ (¬ p41) ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p12 := by
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
  have u4 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1103 := by
    exact h35504
  rcases h26959 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u0)
  · exact False.elim (u6 q7)

theorem step35689 (p124 p185 p265 p576 p664 p897 p923 p1076 : Prop)
    (h35502 : p664)
    (h26979 : (¬ p265) ∨ p124 ∨ p897 ∨ (¬ p576) ∨ (¬ p923) ∨ (¬ p664) ∨ p185 ∨ (¬ p1076)) : p897 ∨ (¬ p265) ∨ p124 ∨ (¬ p576) ∨ (¬ p923) ∨ p185 ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p897) := fun hu => hn (Or.inl hu)
  have u1 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p923 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p664 := by
    exact h35502
  rcases h26979 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (u2 q1)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u7)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u6)

theorem step35690 (p3 p41 p166 p195 p283 p576 : Prop)
    (h35556 : p195)
    (h18296 : (¬ p3) ∨ (¬ p41) ∨ (¬ p166) ∨ (¬ p195) ∨ (¬ p283) ∨ (¬ p576)) : (¬ p3) ∨ (¬ p283) ∨ (¬ p166) ∨ (¬ p576) ∨ (¬ p41) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p283 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p166 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p195 := by
    exact h35556
  rcases h18296 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u3)

theorem step35692 (p12 p39 p68 p126 p225 p303 p561 p576 p1055 : Prop)
    (h35495 : p39)
    (h26999 : p12 ∨ p1055 ∨ p126 ∨ (¬ p303) ∨ (¬ p561) ∨ (¬ p68) ∨ p225 ∨ (¬ p576) ∨ (¬ p39)) : p1055 ∨ p126 ∨ p12 ∨ (¬ p303) ∨ (¬ p561) ∨ (¬ p68) ∨ p225 ∨ (¬ p576) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1055) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p39 := by
    exact h35495
  rcases h26999 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u8)

theorem step35694 (p15 p47 p63 p138 p576 : Prop)
    (h35668 : p138)
    (h27004 : (¬ p15) ∨ (¬ p47) ∨ (¬ p138) ∨ (¬ p576) ∨ p63) : (¬ p576) ∨ (¬ p15) ∨ (¬ p47) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p138 := by
    exact h35668
  rcases h27004 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (u3 q4)

theorem step35695 (p41 p83 p124 p189 p496 p576 p980 p1076 : Prop)
    (h35500 : p496)
    (h27006 : (¬ p41) ∨ p980 ∨ (¬ p576) ∨ (¬ p83) ∨ (¬ p124) ∨ p1076 ∨ (¬ p189) ∨ (¬ p496)) : (¬ p576) ∨ p980 ∨ (¬ p41) ∨ (¬ p83) ∨ (¬ p124) ∨ p1076 ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p496 := by
    exact h35500
  rcases h27006 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u7)

theorem step35698 (p48 p138 p422 p423 p576 : Prop)
    (h35668 : p138)
    (h16893 : (¬ p48) ∨ (¬ p138) ∨ (¬ p422) ∨ (¬ p423) ∨ (¬ p576)) : (¬ p423) ∨ (¬ p576) ∨ (¬ p48) ∨ (¬ p422) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p138 := by
    exact h35668
  rcases h16893 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)

theorem step35704 (p17 p138 p165 p242 p1055 p1115 : Prop)
    (h35668 : p138)
    (h27038 : (¬ p165) ∨ p1055 ∨ (¬ p138) ∨ (¬ p1115) ∨ (¬ p242) ∨ (¬ p17)) : (¬ p165) ∨ (¬ p1115) ∨ p1055 ∨ (¬ p242) ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p165 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p138 := by
    exact h35668
  rcases h27038 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step35706 (p41 p63 p101 p124 p125 p331 p424 : Prop)
    (h35686 : p331)
    (h27081 : p124 ∨ p424 ∨ p63 ∨ p41 ∨ p101 ∨ (¬ p331) ∨ p125) : p424 ∨ p41 ∨ p63 ∨ p124 ∨ p101 ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p41) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p331 := by
    exact h35686
  rcases h27081 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (u2 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u6)
  · exact False.elim (u5 q6)

theorem step35708 (p16 p495 p633 p665 p789 p790 p1076 : Prop)
    (h35539 : p16)
    (h27096 : p1076 ∨ (¬ p633) ∨ (¬ p665) ∨ p789 ∨ (¬ p16) ∨ p790 ∨ p495) : p790 ∨ (¬ p633) ∨ p1076 ∨ (¬ p665) ∨ p789 ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p790) := fun hu => hn (Or.inl hu)
  have u1 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p16 := by
    exact h35539
  rcases h27096 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (u4 q3)
  · exact False.elim (q4 u6)
  · exact False.elim (u0 q5)
  · exact False.elim (u5 q6)

theorem step35710 (p84 p189 p419 p495 p582 p595 p789 p795 p1195 : Prop)
    (h35574 : p582)
    (h27113 : (¬ p1195) ∨ (¬ p789) ∨ p189 ∨ p595 ∨ (¬ p582) ∨ (¬ p419) ∨ p495 ∨ (¬ p795) ∨ (¬ p84)) : (¬ p1195) ∨ (¬ p789) ∨ p189 ∨ p595 ∨ (¬ p419) ∨ p495 ∨ (¬ p795) ∨ (¬ p84) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p795 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p582 := by
    exact h35574
  rcases h27113 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u2 q2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step35711 (p84 p189 p422 p495 p582 p595 p1000 p1287 : Prop)
    (h35574 : p582)
    (h27114 : p495 ∨ (¬ p84) ∨ p595 ∨ (¬ p582) ∨ (¬ p1000) ∨ p189 ∨ (¬ p1287) ∨ p422) : p595 ∨ (¬ p84) ∨ p495 ∨ (¬ p1000) ∨ p189 ∨ (¬ p1287) ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p595) := fun hu => hn (Or.inl hu)
  have u1 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p582 := by
    exact h35574
  rcases h27114 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u3)
  · exact False.elim (u4 q5)
  · exact False.elim (q6 u5)
  · exact False.elim (u6 q7)

theorem step35713 (p3 p5 p163 p331 p420 p424 p495 : Prop)
    (h35686 : p331)
    (h27125 : p3 ∨ p424 ∨ p495 ∨ (¬ p5) ∨ p420 ∨ (¬ p331) ∨ (¬ p163)) : p424 ∨ p3 ∨ p495 ∨ (¬ p5) ∨ p420 ∨ (¬ p163) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p331 := by
    exact h35686
  rcases h27125 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u5)

theorem step35714 (p84 p163 p189 p225 p495 p582 p595 p906 : Prop)
    (h35574 : p582)
    (h27126 : (¬ p906) ∨ (¬ p84) ∨ p595 ∨ p495 ∨ (¬ p163) ∨ p225 ∨ (¬ p582) ∨ p189) : (¬ p906) ∨ (¬ p84) ∨ p595 ∨ p495 ∨ (¬ p163) ∨ p225 ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p906 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p582 := by
    exact h35574
  rcases h27126 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u2 q2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u7)
  · exact False.elim (u6 q7)

theorem step35715 (p347 p420 p495 p836 p1055 p1103 p1115 : Prop)
    (h35646 : p347)
    (h35504 : p1103)
    (h27139 : p1115 ∨ (¬ p836) ∨ p420 ∨ (¬ p347) ∨ (¬ p1055) ∨ (¬ p1103) ∨ p495) : p420 ∨ (¬ p836) ∨ p1115 ∨ (¬ p1055) ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p420) := fun hu => hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p347 := by
    exact h35646
  have u6 : p1103 := by
    exact h35504
  rcases h27139 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (u4 q6)

theorem step35716 (p16 p420 p434 p495 p1330 p1349 p1489 : Prop)
    (h35539 : p16)
    (h27141 : (¬ p434) ∨ (¬ p1489) ∨ (¬ p16) ∨ p420 ∨ p495 ∨ (¬ p1349) ∨ (¬ p1330)) : (¬ p434) ∨ (¬ p1489) ∨ p420 ∨ p495 ∨ (¬ p1349) ∨ (¬ p1330) := by
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
  have u4 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p16 := by
    exact h35539
  rcases h27141 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (u2 q3)
  · exact False.elim (u3 q4)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step35717 (p16 p224 p347 p420 p495 p789 p790 : Prop)
    (h35539 : p16)
    (h35646 : p347)
    (h27142 : p224 ∨ p495 ∨ (¬ p16) ∨ p420 ∨ (¬ p347) ∨ p789 ∨ p790) : p420 ∨ p224 ∨ p495 ∨ p789 ∨ p790 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p420) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p16 := by
    exact h35539
  have u6 : p347 := by
    exact h35646
  rcases h27142 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u5)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u6)
  · exact False.elim (u3 q5)
  · exact False.elim (u4 q6)

theorem step35719 (p8 p16 p238 p455 p495 p836 p1081 p1115 : Prop)
    (h35539 : p16)
    (h27147 : (¬ p1115) ∨ (¬ p455) ∨ (¬ p16) ∨ p8 ∨ (¬ p1081) ∨ (¬ p238) ∨ p836 ∨ p495) : (¬ p1115) ∨ (¬ p455) ∨ p8 ∨ (¬ p1081) ∨ (¬ p238) ∨ p836 ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p16 := by
    exact h35539
  rcases h27147 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u7)
  · exact False.elim (u2 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)
  · exact False.elim (u6 q7)

#print axioms step35719

end NineRUPTrial
