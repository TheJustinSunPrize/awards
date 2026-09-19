import Mathlib.Tactic.Tauto

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

namespace NineRUPTrial

theorem step30704 (p370 p381 p382 p406 p532 p1325 p1333 : Prop)
    (h26869 : p406 ∨ p382)
    (h26931 : p1333 ∨ p1325)
    (h17775 : (¬ p370) ∨ (¬ p381) ∨ (¬ p406) ∨ (¬ p532) ∨ (¬ p1333)) : p382 ∨ p1325 ∨ (¬ p532) ∨ (¬ p370) ∨ (¬ p381) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p370 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p381 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17775 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)

theorem step30705 (p370 p382 p384 p406 p420 p455 p456 p601 : Prop)
    (h26871 : p456 ∨ p455)
    (h26869 : p406 ∨ p382)
    (h26881 : p601 ∨ p420)
    (h19850 : (¬ p370) ∨ (¬ p384) ∨ (¬ p406) ∨ (¬ p456) ∨ (¬ p601)) : p455 ∨ p382 ∨ p420 ∨ (¬ p370) ∨ (¬ p384) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p370 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p384 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19850 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)

theorem step30731 (p303 p363 p382 p387 p420 p497 p601 : Prop)
    (h26867 : p387 ∨ p303)
    (h26881 : p601 ∨ p420)
    (h17155 : (¬ p363) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p497) ∨ (¬ p601)) : (¬ p497) ∨ p303 ∨ (¬ p363) ∨ (¬ p382) ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p497 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p363 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17155 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u6)

theorem step30734 (p105 p163 p167 p210 p363 p382 p789 p795 : Prop)
    (h26843 : p167 ∨ p163)
    (h19091 : (¬ p105) ∨ (¬ p167) ∨ (¬ p210) ∨ (¬ p363) ∨ (¬ p382) ∨ (¬ p789) ∨ (¬ p795)) : (¬ p363) ∨ (¬ p210) ∨ (¬ p105) ∨ (¬ p382) ∨ (¬ p795) ∨ (¬ p789) ∨ p163 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p363 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p795 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19091 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u4)

theorem step30735 (p10 p209 p303 p323 p363 p382 p387 : Prop)
    (h26867 : p387 ∨ p303)
    (h26861 : p323 ∨ p10)
    (h16709 : (¬ p209) ∨ (¬ p323) ∨ (¬ p363) ∨ (¬ p382) ∨ (¬ p387)) : p303 ∨ (¬ p382) ∨ (¬ p363) ∨ (¬ p209) ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p363 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16709 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)

theorem step30736 (p14 p105 p210 p229 p363 p382 p1193 p1286 : Prop)
    (h26849 : p229 ∨ p14)
    (h18690 : (¬ p105) ∨ (¬ p210) ∨ (¬ p229) ∨ (¬ p363) ∨ (¬ p382) ∨ (¬ p1193) ∨ (¬ p1286)) : (¬ p105) ∨ (¬ p363) ∨ p14 ∨ (¬ p210) ∨ (¬ p382) ∨ (¬ p1286) ∨ (¬ p1193) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p363 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18690 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u5)

theorem step30738 (p44 p90 p189 p193 p234 p265 p303 p327 p363 p382 p387 p576 : Prop)
    (h26867 : p387 ∨ p303)
    (h26586 : p90)
    (h26845 : p193 ∨ p189)
    (h19584 : (¬ p44) ∨ (¬ p90) ∨ (¬ p193) ∨ (¬ p234) ∨ (¬ p265) ∨ (¬ p327) ∨ (¬ p363) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p576)) : (¬ p382) ∨ p303 ∨ (¬ p576) ∨ (¬ p234) ∨ p189 ∨ (¬ p327) ∨ (¬ p265) ∨ (¬ p44) ∨ (¬ p363) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p327 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p363 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p90 := by
    exact h26586
  have u11 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19584 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u0)
  · exact False.elim (q8 u9)
  · exact False.elim (q9 u2)

theorem step30739 (p5 p6 p10 p63 p351 p836 p840 p918 p928 : Prop)
    (h26895 : p840 ∨ p836)
    (h26901 : p928 ∨ p918)
    (h20644 : (¬ p5) ∨ (¬ p6) ∨ (¬ p10) ∨ (¬ p63) ∨ (¬ p351) ∨ (¬ p840) ∨ (¬ p928)) : (¬ p10) ∨ (¬ p351) ∨ (¬ p6) ∨ p836 ∨ p918 ∨ (¬ p63) ∨ (¬ p5) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20644 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u8)

theorem step30742 (p303 p328 p387 p419 : Prop)
    (h26867 : p387 ∨ p303)
    (h12556 : (¬ p328) ∨ (¬ p387) ∨ (¬ p419)) : p303 ∨ (¬ p419) ∨ (¬ p328) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p328 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h12556 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)

theorem step30743 (p328 p368 p382 p406 p419 p421 p439 p1604 : Prop)
    (h26869 : p406 ∨ p382)
    (h17813 : (¬ p328) ∨ (¬ p368) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p421) ∨ (¬ p439) ∨ (¬ p1604)) : (¬ p439) ∨ p382 ∨ (¬ p368) ∨ (¬ p419) ∨ (¬ p421) ∨ (¬ p1604) ∨ (¬ p328) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p439 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p368 := by
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
  have u5 : p1604 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p328 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17813 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u5)

theorem step30748 (p39 p63 p68 p327 p382 p406 p419 p420 p475 p495 : Prop)
    (h26869 : p406 ∨ p382)
    (h17789 : (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p327) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p420) ∨ (¬ p475) ∨ (¬ p495)) : p382 ∨ (¬ p68) ∨ (¬ p475) ∨ (¬ p419) ∨ (¬ p327) ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p63) ∨ (¬ p39) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p475 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p327 := by
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
  have u7 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17789 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u2)
  · exact False.elim (q8 u6)

theorem step30749 (p124 p304 p327 p382 p406 p419 p420 p494 p617 p633 : Prop)
    (h26869 : p406 ∨ p382)
    (h26859 : p304 ∨ p124)
    (h16190 : (¬ p304) ∨ (¬ p327) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p420) ∨ (¬ p494) ∨ (¬ p617) ∨ (¬ p633)) : p382 ∨ (¬ p420) ∨ (¬ p419) ∨ (¬ p327) ∨ (¬ p633) ∨ p124 ∨ (¬ p494) ∨ (¬ p617) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p327 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p617 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h16190 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step30751 (p17 p140 p189 p256 p326 p424 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h26853 : p256 ∨ p17)
    (h16234 : (¬ p140) ∨ (¬ p189) ∨ (¬ p256) ∨ (¬ p326) ∨ (¬ p796)) : p424 ∨ p17 ∨ (¬ p326) ∨ (¬ p140) ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p326 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p140 := by
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
  have u6 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16234 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step30752 (p2 p121 p211 p227 p326 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h20254 : (¬ p2) ∨ (¬ p211) ∨ (¬ p227) ∨ (¬ p326) ∨ (¬ p1206)) : (¬ p2) ∨ p121 ∨ (¬ p211) ∨ (¬ p227) ∨ (¬ p326) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p121) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p326 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20254 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)

theorem step30753 (p126 p143 p303 p324 p387 p419 : Prop)
    (h26867 : p387 ∨ p303)
    (h16183 : (¬ p126) ∨ (¬ p143) ∨ (¬ p324) ∨ (¬ p387) ∨ (¬ p419)) : p303 ∨ (¬ p324) ∨ (¬ p126) ∨ (¬ p143) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p324 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p143 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h16183 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)

theorem step30754 (p101 p102 p324 p364 p382 p406 p419 : Prop)
    (h26869 : p406 ∨ p382)
    (h26837 : p102 ∨ p101)
    (h24194 : (¬ p364) ∨ (¬ p324) ∨ (¬ p102) ∨ (¬ p419) ∨ (¬ p406)) : (¬ p324) ∨ p382 ∨ (¬ p419) ∨ (¬ p364) ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p324 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p364 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h24194 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step30756 (p125 p213 p303 p324 p362 p387 p419 : Prop)
    (h26867 : p387 ∨ p303)
    (h26865 : p362 ∨ p125)
    (h17772 : (¬ p213) ∨ (¬ p324) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p419)) : (¬ p324) ∨ p303 ∨ p125 ∨ (¬ p213) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p324 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p213 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17772 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)

theorem step30757 (p101 p102 p324 p434 p435 : Prop)
    (h26837 : p102 ∨ p101)
    (h24196 : (¬ p434) ∨ (¬ p324) ∨ (¬ p102) ∨ (¬ p435)) : (¬ p434) ∨ (¬ p324) ∨ p101 ∨ (¬ p435) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p324 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h24196 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)

theorem step30759 (p303 p324 p387 p419 p420 p601 : Prop)
    (h26867 : p387 ∨ p303)
    (h26881 : p601 ∨ p420)
    (h26059 : (¬ p601) ∨ (¬ p387) ∨ (¬ p324) ∨ (¬ p419)) : (¬ p324) ∨ p303 ∨ p420 ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p324 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h26059 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)

theorem step30760 (p125 p213 p324 p362 p434 p435 : Prop)
    (h26865 : p362 ∨ p125)
    (h17787 : (¬ p213) ∨ (¬ p324) ∨ (¬ p362) ∨ (¬ p434) ∨ (¬ p435)) : (¬ p434) ∨ (¬ p435) ∨ (¬ p213) ∨ p125 ∨ (¬ p324) := by
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
  have u2 : p213 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p324 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17787 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)

theorem step30763 (p18 p234 p324 p1187 : Prop)
    (h26920 : (¬ p234) ∨ (¬ p1187))
    (h15044 : (¬ p18) ∨ (¬ p324) ∨ p1187) : (¬ p324) ∨ (¬ p18) ∨ (¬ p234) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p324 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1187) := by
    rcases h26920 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h15044 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (u3 q2)

theorem step30764 (p309 p1055 p1076 p1077 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h12228 : (¬ p309) ∨ (¬ p1055) ∨ (¬ p1077)) : p1076 ∨ (¬ p309) ∨ (¬ p1055) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1076) := fun hu => hn (Or.inl hu)
  have u1 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h12228 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)

theorem step30766 (p63 p85 p308 p309 : Prop)
    (h26835 : p85 ∨ p63)
    (h18847 : (¬ p85) ∨ p308 ∨ (¬ p309)) : p308 ∨ p63 ∨ (¬ p309) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p308) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p63) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18847 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)

theorem step30767 (p41 p45 p189 p193 p224 p309 p382 p542 p633 p636 p657 p709 p801 p1385 p1393 : Prop)
    (h26885 : p636 ∨ p633)
    (h26887 : p657 ∨ p224)
    (h26933 : p1393 ∨ p1385)
    (h26845 : p193 ∨ p189)
    (h26831 : p45 ∨ p41)
    (h18550 : (¬ p45) ∨ (¬ p193) ∨ (¬ p309) ∨ (¬ p382) ∨ (¬ p542) ∨ (¬ p636) ∨ (¬ p657) ∨ (¬ p709) ∨ (¬ p801) ∨ (¬ p1393)) : (¬ p709) ∨ (¬ p309) ∨ p633 ∨ p224 ∨ p1385 ∨ p189 ∨ (¬ p542) ∨ (¬ p801) ∨ p41 ∨ (¬ p382) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p709 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p633) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p801 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u12 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u13 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u14 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h18550 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u14)
  · exact False.elim (q1 u13)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)
  · exact False.elim (q7 u0)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u12)

theorem step30769 (p8 p108 p121 p225 p309 p544 p710 p1080 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26877 : p544 ∨ p225)
    (h26889 : p710 ∨ p8)
    (h16355 : (¬ p108) ∨ (¬ p309) ∨ (¬ p544) ∨ (¬ p710) ∨ (¬ p1080) ∨ (¬ p1206)) : p121 ∨ p225 ∨ (¬ p309) ∨ (¬ p108) ∨ p8 ∨ (¬ p1080) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1080 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16355 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)

theorem step30770 (p8 p108 p225 p258 p309 p544 p710 : Prop)
    (h26877 : p544 ∨ p225)
    (h26889 : p710 ∨ p8)
    (h22741 : (¬ p710) ∨ (¬ p108) ∨ (¬ p309) ∨ (¬ p258) ∨ (¬ p544)) : (¬ p108) ∨ p225 ∨ (¬ p309) ∨ (¬ p258) ∨ p8 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h22741 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)

theorem step30771 (p8 p309 p344 p710 : Prop)
    (h26889 : p710 ∨ p8)
    (h9310 : (¬ p309) ∨ (¬ p344) ∨ (¬ p710)) : (¬ p344) ∨ (¬ p309) ∨ p8 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h9310 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)

theorem step30773 (p101 p143 p287 p309 p1055 p1115 p1116 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h19615 : (¬ p101) ∨ (¬ p143) ∨ (¬ p287) ∨ (¬ p309) ∨ (¬ p1055) ∨ (¬ p1116)) : (¬ p287) ∨ (¬ p101) ∨ (¬ p1055) ∨ p1115 ∨ (¬ p143) ∨ (¬ p309) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p143 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19615 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)

theorem step30774 (p8 p101 p143 p287 p309 p710 p836 p840 : Prop)
    (h26889 : p710 ∨ p8)
    (h26895 : p840 ∨ p836)
    (h20095 : (¬ p101) ∨ (¬ p143) ∨ (¬ p287) ∨ (¬ p309) ∨ (¬ p710) ∨ (¬ p840)) : (¬ p101) ∨ (¬ p309) ∨ p8 ∨ (¬ p287) ∨ (¬ p143) ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p143 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20095 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)

theorem step30776 (p11 p258 p308 p1055 p1082 p1443 : Prop)
    (h26935 : p1443 ∨ p11)
    (h20243 : (¬ p258) ∨ (¬ p308) ∨ (¬ p1055) ∨ (¬ p1082) ∨ (¬ p1443)) : (¬ p258) ∨ (¬ p308) ∨ p11 ∨ (¬ p1055) ∨ (¬ p1082) := by
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
  have u2 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1082 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20243 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)

theorem step30777 (p308 p344 p836 p1055 p1115 p1116 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h20454 : (¬ p308) ∨ (¬ p344) ∨ (¬ p836) ∨ (¬ p1055) ∨ (¬ p1116)) : (¬ p836) ∨ (¬ p344) ∨ p1115 ∨ (¬ p308) ∨ (¬ p1055) := by
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
  have u3 : p308 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20454 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)

theorem step30826 (p125 p268 p362 p515 p576 p581 p1385 : Prop)
    (h26865 : p362 ∨ p125)
    (h26879 : p581 ∨ p576)
    (h17143 : (¬ p268) ∨ (¬ p362) ∨ (¬ p515) ∨ (¬ p581) ∨ (¬ p1385)) : (¬ p515) ∨ (¬ p1385) ∨ p125 ∨ (¬ p268) ∨ p576 := by
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
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p268 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17143 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)

theorem step30827 (p125 p268 p303 p362 p387 p514 p789 p858 : Prop)
    (h26867 : p387 ∨ p303)
    (h26865 : p362 ∨ p125)
    (h26897 : p858 ∨ p789)
    (h18086 : (¬ p268) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p514) ∨ (¬ p858)) : (¬ p514) ∨ p303 ∨ p125 ∨ p789 ∨ (¬ p268) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p514 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p268 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18086 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u7)

theorem step30828 (p8 p189 p193 p243 p344 p422 p710 p1040 p1076 p1256 : Prop)
    (h26929 : p1256 ∨ p422)
    (h26845 : p193 ∨ p189)
    (h26889 : p710 ∨ p8)
    (h18751 : (¬ p193) ∨ (¬ p243) ∨ (¬ p344) ∨ (¬ p710) ∨ (¬ p1040) ∨ (¬ p1076) ∨ (¬ p1256)) : p422 ∨ (¬ p344) ∨ p189 ∨ (¬ p1076) ∨ (¬ p243) ∨ p8 ∨ (¬ p1040) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p422) := fun hu => hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p243 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1040 := by
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
  have u9 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18751 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step30829 (p8 p189 p193 p243 p422 p710 p734 p1035 p1256 p1335 : Prop)
    (h26929 : p1256 ∨ p422)
    (h26845 : p193 ∨ p189)
    (h26889 : p710 ∨ p8)
    (h18754 : (¬ p193) ∨ (¬ p243) ∨ (¬ p710) ∨ (¬ p734) ∨ (¬ p1035) ∨ (¬ p1256) ∨ (¬ p1335)) : p422 ∨ p189 ∨ (¬ p243) ∨ (¬ p1035) ∨ p8 ∨ (¬ p734) ∨ (¬ p1335) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p422) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p243 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1335 := by
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
    · exact False.elim (u1 q1)
  have u9 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18754 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u6)

theorem step30831 (p63 p85 p88 p243 p344 p346 p595 p756 p769 p901 : Prop)
    (h26863 : p346 ∨ p344)
    (h26835 : p85 ∨ p63)
    (h18704 : (¬ p85) ∨ (¬ p88) ∨ (¬ p243) ∨ (¬ p346) ∨ (¬ p595) ∨ (¬ p756) ∨ (¬ p769) ∨ (¬ p901)) : (¬ p756) ∨ p344 ∨ (¬ p595) ∨ p63 ∨ (¬ p243) ∨ (¬ p88) ∨ (¬ p769) ∨ (¬ p901) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p243 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p769 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p901 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18704 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u7)

theorem step30832 (p6 p8 p121 p127 p186 p243 p710 p734 p1335 p1452 : Prop)
    (h26889 : p710 ∨ p8)
    (h26839 : p127 ∨ p6)
    (h16945 : (¬ p121) ∨ (¬ p127) ∨ (¬ p186) ∨ (¬ p243) ∨ (¬ p710) ∨ (¬ p734) ∨ (¬ p1335) ∨ (¬ p1452)) : (¬ p1452) ∨ (¬ p121) ∨ (¬ p186) ∨ (¬ p243) ∨ (¬ p1335) ∨ p8 ∨ (¬ p734) ∨ p6 := by
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
  have u2 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p243 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u9 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h16945 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u0)

theorem step30834 (p6 p10 p38 p49 p84 p242 p303 p836 p840 p1055 p1061 p1115 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h26895 : p840 ∨ p836)
    (h20119 : (¬ p6) ∨ (¬ p10) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p242) ∨ (¬ p303) ∨ (¬ p840) ∨ (¬ p1061) ∨ (¬ p1115)) : (¬ p38) ∨ (¬ p10) ∨ (¬ p6) ∨ (¬ p242) ∨ (¬ p84) ∨ p1055 ∨ (¬ p49) ∨ (¬ p1115) ∨ (¬ p303) ∨ p836 := by
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
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u11 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h20119 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u11)
  · exact False.elim (q8 u10)
  · exact False.elim (q9 u7)

theorem step30836 (p90 p242 p918 p1055 p1061 p1115 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h26586 : p90)
    (h17230 : (¬ p90) ∨ (¬ p242) ∨ (¬ p918) ∨ (¬ p1061) ∨ (¬ p1115)) : (¬ p242) ∨ (¬ p1115) ∨ p1055 ∨ (¬ p918) := by
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
  have u2 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p90 := by
    exact h26586
  rcases h17230 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u1)

theorem step30838 (p6 p8 p13 p121 p194 p242 p836 p1115 p1116 p1206 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h26923 : p1206 ∨ p121)
    (h20304 : (¬ p6) ∨ (¬ p8) ∨ (¬ p13) ∨ (¬ p194) ∨ (¬ p242) ∨ (¬ p836) ∨ (¬ p1116) ∨ (¬ p1206)) : (¬ p836) ∨ p1115 ∨ (¬ p8) ∨ (¬ p194) ∨ (¬ p242) ∨ (¬ p6) ∨ p121 ∨ (¬ p13) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1115) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p8 := by
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
  have u5 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p121) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20304 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u9)

theorem step30840 (p12 p189 p225 p242 p544 p1036 p1055 p1061 : Prop)
    (h26907 : p1036 ∨ p12)
    (h26877 : p544 ∨ p225)
    (h26909 : p1061 ∨ p1055)
    (h19160 : (¬ p189) ∨ (¬ p242) ∨ (¬ p544) ∨ (¬ p1036) ∨ (¬ p1061)) : (¬ p242) ∨ p12 ∨ (¬ p189) ∨ p225 ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19160 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)

theorem step30843 (p242 p283 p516 p790 p814 p1055 p1061 p1115 : Prop)
    (h26893 : p814 ∨ p790)
    (h26909 : p1061 ∨ p1055)
    (h16515 : (¬ p242) ∨ (¬ p283) ∨ (¬ p516) ∨ (¬ p814) ∨ (¬ p1061) ∨ (¬ p1115)) : (¬ p516) ∨ (¬ p283) ∨ p790 ∨ p1055 ∨ (¬ p1115) ∨ (¬ p242) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p516 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p283 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16515 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u4)

theorem step30869 (p241 p1055 p1115 p1116 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h8743 : (¬ p241) ∨ (¬ p1055) ∨ (¬ p1116)) : (¬ p241) ∨ (¬ p1055) ∨ p1115 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h8743 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)

theorem step30871 (p8 p241 p836 p840 : Prop)
    (h26895 : p840 ∨ p836)
    (h11752 : p8 ∨ (¬ p241) ∨ (¬ p840)) : (¬ p241) ∨ p8 ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p8) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h11752 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)

theorem step30873 (p8 p241 p662 p710 p1115 p1116 : Prop)
    (h26889 : p710 ∨ p8)
    (h26915 : p1116 ∨ p1115)
    (h12232 : (¬ p241) ∨ (¬ p662) ∨ (¬ p710) ∨ (¬ p1116)) : (¬ p241) ∨ p8 ∨ p1115 ∨ (¬ p662) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p8) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p662 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h12232 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step30876 (p8 p224 p241 p710 p918 p1325 : Prop)
    (h26889 : p710 ∨ p8)
    (h18666 : (¬ p224) ∨ (¬ p241) ∨ (¬ p710) ∨ (¬ p918) ∨ (¬ p1325)) : (¬ p241) ∨ p8 ∨ (¬ p918) ∨ (¬ p224) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p8) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p918 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18666 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u4)

theorem step30877 (p8 p241 p286 p344 p710 : Prop)
    (h26889 : p710 ∨ p8)
    (h15504 : (¬ p241) ∨ (¬ p286) ∨ (¬ p344) ∨ (¬ p710)) : (¬ p344) ∨ (¬ p286) ∨ (¬ p241) ∨ p8 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h15504 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)

theorem step30878 (p8 p41 p241 p344 p710 p918 : Prop)
    (h26889 : p710 ∨ p8)
    (h20607 : (¬ p41) ∨ (¬ p241) ∨ (¬ p344) ∨ (¬ p710) ∨ (¬ p918)) : (¬ p241) ∨ (¬ p918) ∨ (¬ p344) ∨ (¬ p41) ∨ p8 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20607 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)

theorem step30879 (p8 p41 p45 p171 p241 p710 p897 p904 p927 : Prop)
    (h26889 : p710 ∨ p8)
    (h26831 : p45 ∨ p41)
    (h26899 : p904 ∨ p897)
    (h20295 : (¬ p45) ∨ (¬ p171) ∨ (¬ p241) ∨ (¬ p710) ∨ (¬ p904) ∨ (¬ p927)) : (¬ p171) ∨ (¬ p241) ∨ p8 ∨ p41 ∨ p897 ∨ (¬ p927) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p171 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p927 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20295 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u5)

theorem step30880 (p8 p90 p106 p163 p189 p193 p241 p344 p710 p918 : Prop)
    (h26586 : p90)
    (h26889 : p710 ∨ p8)
    (h26845 : p193 ∨ p189)
    (h20037 : (¬ p90) ∨ (¬ p106) ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p241) ∨ (¬ p344) ∨ (¬ p710) ∨ (¬ p918)) : (¬ p241) ∨ (¬ p918) ∨ (¬ p163) ∨ (¬ p106) ∨ p8 ∨ (¬ p344) ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p918 := by
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
  have u4 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p90 := by
    exact h26586
  have u8 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20037 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u1)

theorem step30881 (p14 p44 p90 p189 p193 p225 p241 p544 p918 p1055 p1076 p1077 : Prop)
    (h26877 : p544 ∨ p225)
    (h26845 : p193 ∨ p189)
    (h26911 : p1077 ∨ p1076)
    (h26586 : p90)
    (h19327 : (¬ p14) ∨ (¬ p44) ∨ (¬ p90) ∨ (¬ p193) ∨ (¬ p241) ∨ (¬ p544) ∨ (¬ p918) ∨ (¬ p1055) ∨ (¬ p1077)) : p225 ∨ (¬ p918) ∨ (¬ p14) ∨ (¬ p44) ∨ p189 ∨ (¬ p241) ∨ (¬ p1055) ∨ p1076 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p225) := fun hu => hn (Or.inl hu)
  have u1 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p90 := by
    exact h26586
  rcases h19327 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u10)

theorem step30882 (p8 p12 p14 p44 p90 p189 p193 p241 p668 p710 p918 : Prop)
    (h26889 : p710 ∨ p8)
    (h26845 : p193 ∨ p189)
    (h26586 : p90)
    (h17356 : (¬ p12) ∨ (¬ p14) ∨ (¬ p44) ∨ (¬ p90) ∨ (¬ p193) ∨ (¬ p241) ∨ (¬ p668) ∨ (¬ p710) ∨ (¬ p918)) : (¬ p241) ∨ (¬ p918) ∨ (¬ p44) ∨ p8 ∨ (¬ p668) ∨ p189 ∨ (¬ p12) ∨ (¬ p14) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p90 := by
    exact h26586
  rcases h17356 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u1)

theorem step30883 (p8 p224 p240 p710 p789 p839 : Prop)
    (h26889 : p710 ∨ p8)
    (h17146 : (¬ p224) ∨ (¬ p240) ∨ (¬ p710) ∨ (¬ p789) ∨ (¬ p839)) : (¬ p789) ∨ (¬ p224) ∨ p8 ∨ (¬ p839) ∨ (¬ p240) := by
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
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p839 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p240 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17146 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u3)

theorem step30884 (p224 p240 p382 p657 p709 p836 p840 : Prop)
    (h26887 : p657 ∨ p224)
    (h26895 : p840 ∨ p836)
    (h19017 : (¬ p240) ∨ (¬ p382) ∨ (¬ p657) ∨ (¬ p709) ∨ (¬ p840)) : p224 ∨ (¬ p709) ∨ p836 ∨ (¬ p240) ∨ (¬ p382) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p224) := fun hu => hn (Or.inl hu)
  have u1 : p709 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p240 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19017 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)

theorem step30885 (p225 p239 p536 p544 p789 p790 p814 p858 p940 p1325 : Prop)
    (h26893 : p814 ∨ p790)
    (h26897 : p858 ∨ p789)
    (h26877 : p544 ∨ p225)
    (h19149 : (¬ p239) ∨ (¬ p536) ∨ (¬ p544) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p940) ∨ (¬ p1325)) : (¬ p940) ∨ (¬ p536) ∨ p790 ∨ p789 ∨ p225 ∨ (¬ p1325) ∨ (¬ p239) := by
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
  have u2 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p239 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19149 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u5)

theorem step30887 (p6 p10 p188 p239 p438 p980 p983 p1055 p1061 p1335 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h26903 : p983 ∨ p980)
    (h20359 : (¬ p6) ∨ (¬ p10) ∨ (¬ p188) ∨ (¬ p239) ∨ (¬ p438) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1335)) : (¬ p10) ∨ p1055 ∨ (¬ p1335) ∨ p980 ∨ (¬ p438) ∨ (¬ p6) ∨ (¬ p239) ∨ (¬ p188) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p239 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p188 := by
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
    · exact False.elim (u3 q1)
  rcases h20359 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u2)

theorem step30889 (p8 p189 p239 p344 p346 p422 p1044 p1076 p1077 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26863 : p346 ∨ p344)
    (h18184 : (¬ p8) ∨ (¬ p189) ∨ (¬ p239) ∨ (¬ p346) ∨ (¬ p422) ∨ (¬ p1044) ∨ (¬ p1077)) : (¬ p422) ∨ p1076 ∨ p344 ∨ (¬ p239) ∨ (¬ p8) ∨ (¬ p1044) ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p239 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1044 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18184 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u7)

theorem step30890 (p157 p160 p189 p239 p419 p424 p665 p796 p980 : Prop)
    (h26891 : p796 ∨ p424)
    (h20016 : (¬ p157) ∨ (¬ p160) ∨ (¬ p189) ∨ (¬ p239) ∨ (¬ p419) ∨ (¬ p665) ∨ (¬ p796) ∨ (¬ p980)) : p424 ∨ (¬ p160) ∨ (¬ p157) ∨ (¬ p665) ∨ (¬ p980) ∨ (¬ p419) ∨ (¬ p189) ∨ (¬ p239) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p157 := by
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
  have u5 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p239 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h20016 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u4)

theorem step30891 (p6 p8 p134 p142 p188 p224 p239 p422 p657 p1004 : Prop)
    (h26887 : p657 ∨ p224)
    (h26841 : p142 ∨ p134)
    (h19559 : (¬ p6) ∨ (¬ p8) ∨ (¬ p142) ∨ (¬ p188) ∨ (¬ p239) ∨ (¬ p422) ∨ (¬ p657) ∨ (¬ p1004)) : (¬ p422) ∨ (¬ p1004) ∨ (¬ p8) ∨ (¬ p188) ∨ p224 ∨ (¬ p239) ∨ p134 ∨ (¬ p6) := by
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
  have u2 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p239 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19559 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u1)

theorem step30922 (p6 p127 p208 p219 p220 p221 p222 p223 : Prop)
    (h26838 : (¬ p6) ∨ (¬ p127))
    (h1089 : p127 ∨ p208 ∨ (¬ p219) ∨ (¬ p220) ∨ (¬ p221) ∨ (¬ p222) ∨ (¬ p223)) : p208 ∨ (¬ p220) ∨ (¬ p6) ∨ (¬ p223) ∨ (¬ p219) ∨ (¬ p222) ∨ (¬ p221) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p208) := fun hu => hn (Or.inl hu)
  have u1 : p220 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p223 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p219 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p222 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p221 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p127) := by
    rcases h26838 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h1089 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u7 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u3)

theorem step30926 (p6 p127 p208 p214 p215 p216 p217 p218 : Prop)
    (h26838 : (¬ p6) ∨ (¬ p127))
    (h1064 : p127 ∨ p208 ∨ (¬ p214) ∨ (¬ p215) ∨ (¬ p216) ∨ (¬ p217) ∨ (¬ p218)) : p208 ∨ (¬ p217) ∨ (¬ p6) ∨ (¬ p216) ∨ (¬ p214) ∨ (¬ p215) ∨ (¬ p218) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p208) := fun hu => hn (Or.inl hu)
  have u1 : p217 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p216 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p214 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p215 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p218 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p127) := by
    rcases h26838 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h1064 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u7 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u6)

theorem step30927 (p10 p213 p303 p368 p382 p406 : Prop)
    (h26869 : p406 ∨ p382)
    (h17636 : (¬ p10) ∨ (¬ p213) ∨ (¬ p303) ∨ (¬ p368) ∨ (¬ p406)) : (¬ p10) ∨ p382 ∨ (¬ p213) ∨ (¬ p368) ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p213 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17636 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)

theorem step30928 (p101 p213 p286 p310 p1055 p1061 p1115 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h17549 : (¬ p101) ∨ (¬ p213) ∨ (¬ p286) ∨ (¬ p310) ∨ (¬ p1061) ∨ (¬ p1115)) : (¬ p101) ∨ (¬ p286) ∨ (¬ p310) ∨ (¬ p213) ∨ p1055 ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p213 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17549 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u5)

theorem step30954 (p124 p134 p208 p224 p344 p422 p657 p1140 p1159 p1256 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26887 : p657 ∨ p224)
    (h26929 : p1256 ∨ p422)
    (h19470 : (¬ p124) ∨ (¬ p134) ∨ (¬ p208) ∨ (¬ p344) ∨ (¬ p657) ∨ (¬ p1159) ∨ (¬ p1256)) : (¬ p208) ∨ p1140 ∨ p224 ∨ (¬ p134) ∨ (¬ p124) ∨ (¬ p344) ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p208 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1140) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19470 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u9)

theorem step30956 (p195 p382 p424 p480 p665 p796 p980 p1140 p1253 p1508 : Prop)
    (h26891 : p796 ∨ p424)
    (h18729 : (¬ p195) ∨ (¬ p382) ∨ (¬ p480) ∨ (¬ p665) ∨ (¬ p796) ∨ (¬ p980) ∨ (¬ p1140) ∨ (¬ p1253) ∨ (¬ p1508)) : p424 ∨ (¬ p1253) ∨ (¬ p980) ∨ (¬ p1508) ∨ (¬ p382) ∨ (¬ p1140) ∨ (¬ p195) ∨ (¬ p480) ∨ (¬ p665) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p1253 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p480 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h18729 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u3)

theorem step30957 (p2 p17 p41 p45 p190 p419 p481 p576 p581 p996 p1325 p1333 : Prop)
    (h26905 : p996 ∨ p419)
    (h26831 : p45 ∨ p41)
    (h26931 : p1333 ∨ p1325)
    (h26879 : p581 ∨ p576)
    (h26873 : p481 ∨ p2)
    (h19640 : (¬ p17) ∨ (¬ p45) ∨ (¬ p190) ∨ (¬ p481) ∨ (¬ p581) ∨ (¬ p996) ∨ (¬ p1333)) : p419 ∨ p41 ∨ (¬ p190) ∨ p1325 ∨ p576 ∨ (¬ p17) ∨ p2 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p41) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19640 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u9)

theorem step30959 (p3 p172 p1038 p1115 p1116 p1140 p1159 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26915 : p1116 ∨ p1115)
    (h19907 : (¬ p3) ∨ (¬ p172) ∨ (¬ p1038) ∨ (¬ p1116) ∨ (¬ p1159)) : p1140 ∨ p1115 ∨ (¬ p1038) ∨ (¬ p172) ∨ (¬ p3) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1115) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1038 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p172 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19907 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step30960 (p14 p172 p234 p480 p656 p836 p840 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26895 : p840 ∨ p836)
    (h20532 : (¬ p14) ∨ (¬ p172) ∨ (¬ p480) ∨ (¬ p656) ∨ (¬ p840) ∨ (¬ p1187)) : p234 ∨ (¬ p656) ∨ (¬ p480) ∨ (¬ p172) ∨ (¬ p14) ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : p656 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p480 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p172 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20532 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u6)

theorem step30961 (p160 p172 p1037 p1057 p1115 p1116 p1465 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h17717 : (¬ p160) ∨ (¬ p172) ∨ (¬ p1037) ∨ (¬ p1057) ∨ (¬ p1116) ∨ (¬ p1465)) : (¬ p1037) ∨ (¬ p160) ∨ (¬ p1057) ∨ (¬ p172) ∨ p1115 ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1037 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1057 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p172 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17717 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u5)

theorem step30962 (p10 p17 p140 p171 p189 p224 p241 p256 p323 p347 p382 p657 p709 : Prop)
    (h26861 : p323 ∨ p10)
    (h26853 : p256 ∨ p17)
    (h26887 : p657 ∨ p224)
    (h18649 : (¬ p140) ∨ (¬ p171) ∨ (¬ p189) ∨ (¬ p241) ∨ (¬ p256) ∨ (¬ p323) ∨ (¬ p347) ∨ (¬ p382) ∨ (¬ p657) ∨ (¬ p709)) : (¬ p171) ∨ (¬ p241) ∨ (¬ p709) ∨ (¬ p382) ∨ (¬ p347) ∨ p10 ∨ p17 ∨ p224 ∨ (¬ p140) ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p171 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p709 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u11 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u12 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h18649 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u3)
  · exact False.elim (q8 u12)
  · exact False.elim (q9 u2)

theorem step30963 (p17 p171 p189 p224 p256 p258 p288 p690 p709 p728 p926 p1102 : Prop)
    (h26855 : p288 ∨ p258)
    (h26853 : p256 ∨ p17)
    (h18652 : (¬ p171) ∨ (¬ p189) ∨ (¬ p224) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p690) ∨ (¬ p709) ∨ (¬ p728) ∨ (¬ p926) ∨ (¬ p1102)) : (¬ p1102) ∨ (¬ p728) ∨ (¬ p189) ∨ p258 ∨ (¬ p224) ∨ (¬ p926) ∨ (¬ p171) ∨ (¬ p709) ∨ p17 ∨ (¬ p690) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p926 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p171 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p709 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h18652 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u0)

theorem step30964 (p171 p189 p242 p1055 p1061 p1115 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h20291 : (¬ p171) ∨ (¬ p189) ∨ (¬ p242) ∨ (¬ p1061) ∨ (¬ p1115)) : p1055 ∨ (¬ p1115) ∨ (¬ p242) ∨ (¬ p189) ∨ (¬ p171) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1055) := fun hu => hn (Or.inl hu)
  have u1 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p171 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h20291 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)

theorem step30965 (p43 p171 p234 p424 p918 p928 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26901 : p928 ∨ p918)
    (h20416 : (¬ p43) ∨ (¬ p171) ∨ (¬ p424) ∨ (¬ p928) ∨ (¬ p1187)) : (¬ p171) ∨ p234 ∨ (¬ p424) ∨ (¬ p43) ∨ p918 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p171 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p234) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20416 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step30969 (p10 p101 p102 p125 p171 p185 p187 p211 p224 p237 p362 p790 p814 p835 : Prop)
    (h26893 : p814 ∨ p790)
    (h26851 : p237 ∨ p185)
    (h26837 : p102 ∨ p101)
    (h26865 : p362 ∨ p125)
    (h20333 : (¬ p10) ∨ (¬ p102) ∨ (¬ p171) ∨ (¬ p187) ∨ (¬ p211) ∨ (¬ p224) ∨ (¬ p237) ∨ (¬ p362) ∨ (¬ p814) ∨ (¬ p835)) : (¬ p10) ∨ (¬ p835) ∨ (¬ p187) ∨ (¬ p171) ∨ p790 ∨ (¬ p211) ∨ p185 ∨ (¬ p224) ∨ p101 ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p835 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p171 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u12 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u13 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h20333 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u12)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u11)
  · exact False.elim (q7 u13)
  · exact False.elim (q8 u10)
  · exact False.elim (q9 u1)

theorem step30971 (p170 p185 p189 p193 : Prop)
    (h26845 : p193 ∨ p189)
    (h10852 : (¬ p170) ∨ (¬ p185) ∨ (¬ p193)) : (¬ p185) ∨ p189 ∨ (¬ p170) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p170 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h10852 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)

theorem step30972 (p12 p134 p170 p225 p544 p1036 p1115 p1116 : Prop)
    (h26877 : p544 ∨ p225)
    (h26907 : p1036 ∨ p12)
    (h26915 : p1116 ∨ p1115)
    (h17084 : (¬ p134) ∨ (¬ p170) ∨ (¬ p544) ∨ (¬ p1036) ∨ (¬ p1116)) : p225 ∨ p12 ∨ p1115 ∨ (¬ p170) ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p225) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p170 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17084 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)

theorem step30973 (p8 p14 p170 p229 p560 p710 p836 p840 : Prop)
    (h26849 : p229 ∨ p14)
    (h26895 : p840 ∨ p836)
    (h26889 : p710 ∨ p8)
    (h26062 : (¬ p840) ∨ (¬ p229) ∨ (¬ p560) ∨ (¬ p710) ∨ (¬ p170)) : (¬ p560) ∨ p14 ∨ (¬ p170) ∨ p836 ∨ p8 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p14) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p170 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h26062 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u2)

theorem step30974 (p14 p170 p229 p560 p1055 p1115 p1116 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h26849 : p229 ∨ p14)
    (h26063 : (¬ p1116) ∨ (¬ p229) ∨ (¬ p1055) ∨ (¬ p560) ∨ (¬ p170)) : (¬ p560) ∨ p1115 ∨ p14 ∨ (¬ p1055) ∨ (¬ p170) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1115) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p170 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h26063 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)

theorem step30975 (p63 p170 p1074 p1096 p1099 p1115 p1116 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26915 : p1116 ∨ p1115)
    (h19342 : (¬ p63) ∨ (¬ p170) ∨ (¬ p1074) ∨ (¬ p1099) ∨ (¬ p1116)) : p1096 ∨ p1115 ∨ (¬ p63) ∨ (¬ p170) ∨ (¬ p1074) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1096) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1115) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p170 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19342 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)

theorem step30976 (p3 p170 p191 p225 p226 p836 p840 : Prop)
    (h26847 : p226 ∨ p3)
    (h26895 : p840 ∨ p836)
    (h19576 : (¬ p170) ∨ (¬ p191) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p840)) : p3 ∨ (¬ p225) ∨ p836 ∨ (¬ p191) ∨ (¬ p170) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p170 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19576 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)

theorem step30977 (p8 p170 p210 p305 p422 p710 p836 p840 p1209 : Prop)
    (h26895 : p840 ∨ p836)
    (h26889 : p710 ∨ p8)
    (h20062 : (¬ p170) ∨ (¬ p210) ∨ (¬ p305) ∨ (¬ p422) ∨ (¬ p710) ∨ (¬ p840) ∨ (¬ p1209)) : (¬ p210) ∨ (¬ p422) ∨ p836 ∨ (¬ p305) ∨ (¬ p170) ∨ (¬ p1209) ∨ p8 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p170 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20062 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u5)

theorem step30978 (p15 p18 p19 p170 p326 p424 p796 p1055 p1103 p1115 p1116 : Prop)
    (h26891 : p796 ∨ p424)
    (h26829 : p19 ∨ p18)
    (h26915 : p1116 ∨ p1115)
    (h20499 : (¬ p15) ∨ (¬ p19) ∨ (¬ p170) ∨ (¬ p326) ∨ (¬ p796) ∨ (¬ p1055) ∨ (¬ p1103) ∨ (¬ p1116)) : p424 ∨ (¬ p15) ∨ p18 ∨ (¬ p1103) ∨ (¬ p1055) ∨ (¬ p170) ∨ p1115 ∨ (¬ p326) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p170 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p326 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20499 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u10)

theorem step30980 (p8 p109 p134 p170 p560 p710 p836 p840 : Prop)
    (h26889 : p710 ∨ p8)
    (h26895 : p840 ∨ p836)
    (h19921 : (¬ p109) ∨ (¬ p134) ∨ (¬ p170) ∨ (¬ p560) ∨ (¬ p710) ∨ (¬ p840)) : (¬ p560) ∨ (¬ p170) ∨ (¬ p134) ∨ (¬ p109) ∨ p8 ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p170 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p109 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u7 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19921 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)

theorem step30982 (p2 p14 p17 p64 p168 p185 p229 p234 p237 p576 p581 : Prop)
    (h26849 : p229 ∨ p14)
    (h26879 : p581 ∨ p576)
    (h26851 : p237 ∨ p185)
    (h17183 : (¬ p2) ∨ (¬ p17) ∨ (¬ p64) ∨ (¬ p168) ∨ (¬ p229) ∨ (¬ p234) ∨ (¬ p237) ∨ (¬ p581)) : (¬ p168) ∨ (¬ p234) ∨ p14 ∨ p576 ∨ p185 ∨ (¬ p64) ∨ (¬ p17) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p168 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17183 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u9)

theorem step30983 (p63 p85 p159 p1229 : Prop)
    (h26835 : p85 ∨ p63)
    (h10602 : (¬ p85) ∨ (¬ p159) ∨ (¬ p1229)) : (¬ p1229) ∨ (¬ p159) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h10602 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)

theorem step30985 (p89 p159 p161 p576 p581 p1346 p1508 : Prop)
    (h26879 : p581 ∨ p576)
    (h20600 : (¬ p89) ∨ (¬ p159) ∨ (¬ p161) ∨ (¬ p581) ∨ (¬ p1346) ∨ (¬ p1508)) : (¬ p159) ∨ p576 ∨ (¬ p1508) ∨ (¬ p1346) ∨ (¬ p161) ∨ (¬ p89) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20600 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u2)

theorem step31012 (p8 p157 p160 p344 p710 p1325 : Prop)
    (h26889 : p710 ∨ p8)
    (h20587 : (¬ p157) ∨ (¬ p160) ∨ (¬ p344) ∨ (¬ p710) ∨ (¬ p1325)) : (¬ p157) ∨ (¬ p160) ∨ p8 ∨ (¬ p1325) ∨ (¬ p344) := by
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
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20587 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)

theorem step31013 (p8 p157 p160 p668 p710 p980 : Prop)
    (h26889 : p710 ∨ p8)
    (h19413 : (¬ p157) ∨ (¬ p160) ∨ (¬ p668) ∨ (¬ p710) ∨ (¬ p980)) : (¬ p157) ∨ (¬ p160) ∨ (¬ p980) ∨ p8 ∨ (¬ p668) := by
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
  have u2 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19413 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)

theorem step31014 (p125 p126 p136 p156 p185 p266 p301 p362 : Prop)
    (h26857 : p301 ∨ p126)
    (h26865 : p362 ∨ p125)
    (h18345 : (¬ p136) ∨ (¬ p156) ∨ (¬ p185) ∨ (¬ p266) ∨ (¬ p301) ∨ (¬ p362)) : p126 ∨ (¬ p156) ∨ p125 ∨ (¬ p185) ∨ (¬ p266) ∨ (¬ p136) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p136 := by
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
  rcases h18345 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)

theorem step31017 (p134 p138 p142 p149 p150 p151 p152 p153 : Prop)
    (h26840 : (¬ p134) ∨ (¬ p142))
    (h698 : p138 ∨ p142 ∨ (¬ p149) ∨ (¬ p150) ∨ (¬ p151) ∨ (¬ p152) ∨ (¬ p153)) : (¬ p149) ∨ p138 ∨ (¬ p134) ∨ (¬ p152) ∨ (¬ p153) ∨ (¬ p150) ∨ (¬ p151) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p149 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p138) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p152 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p153 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p150 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p151 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p142) := by
    rcases h26840 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h698 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)

theorem step31019 (p134 p138 p142 p144 p145 p146 p147 p148 : Prop)
    (h26840 : (¬ p134) ∨ (¬ p142))
    (h673 : p138 ∨ p142 ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p147) ∨ (¬ p148)) : p138 ∨ (¬ p147) ∨ (¬ p134) ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p148) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p138) := fun hu => hn (Or.inl hu)
  have u1 : p147 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p144 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p145 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p146 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p148 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p142) := by
    rcases h26840 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h673 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u6)

theorem step31021 (p101 p143 p262 p310 p1055 p1061 p1076 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h16314 : (¬ p101) ∨ (¬ p143) ∨ (¬ p262) ∨ (¬ p310) ∨ (¬ p1061) ∨ (¬ p1076)) : (¬ p101) ∨ (¬ p310) ∨ (¬ p1076) ∨ (¬ p143) ∨ p1055 ∨ (¬ p262) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p143 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16314 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)

theorem step31022 (p2 p6 p126 p127 p143 p420 p424 p495 : Prop)
    (h26839 : p127 ∨ p6)
    (h16868 : (¬ p2) ∨ (¬ p126) ∨ (¬ p127) ∨ (¬ p143) ∨ (¬ p420) ∨ (¬ p424) ∨ (¬ p495)) : (¬ p2) ∨ p6 ∨ (¬ p420) ∨ (¬ p143) ∨ (¬ p424) ∨ (¬ p495) ∨ (¬ p126) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p143 := by
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
  have u6 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16868 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step31023 (p3 p6 p126 p127 p143 p163 p226 p420 p495 : Prop)
    (h26847 : p226 ∨ p3)
    (h26839 : p127 ∨ p6)
    (h19256 : (¬ p126) ∨ (¬ p127) ∨ (¬ p143) ∨ (¬ p163) ∨ (¬ p226) ∨ (¬ p420) ∨ (¬ p495)) : (¬ p420) ∨ p3 ∨ p6 ∨ (¬ p163) ∨ (¬ p495) ∨ (¬ p143) ∨ (¬ p126) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p143 := by
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
    · exact False.elim (u1 q1)
  have u8 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19256 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u4)

theorem step31024 (p10 p17 p143 p420 p495 p499 p601 p790 p1385 : Prop)
    (h26875 : p499 ∨ p495)
    (h26881 : p601 ∨ p420)
    (h18798 : (¬ p10) ∨ (¬ p17) ∨ (¬ p143) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p790) ∨ (¬ p1385)) : (¬ p10) ∨ (¬ p143) ∨ (¬ p790) ∨ (¬ p17) ∨ (¬ p1385) ∨ p495 ∨ p420 := by
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
  have u2 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u8 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18798 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u4)

theorem step31026 (p3 p6 p104 p127 p143 p226 p258 p288 : Prop)
    (h26847 : p226 ∨ p3)
    (h26839 : p127 ∨ p6)
    (h26855 : p288 ∨ p258)
    (h16870 : (¬ p104) ∨ (¬ p127) ∨ (¬ p143) ∨ (¬ p226) ∨ (¬ p288)) : p3 ∨ (¬ p104) ∨ p6 ∨ (¬ p143) ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p143 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16870 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)

theorem step31027 (p121 p143 p576 p1206 p1273 p1495 : Prop)
    (h26923 : p1206 ∨ p121)
    (h17432 : (¬ p143) ∨ (¬ p576) ∨ (¬ p1206) ∨ (¬ p1273) ∨ (¬ p1495)) : (¬ p1495) ∨ p121 ∨ (¬ p576) ∨ (¬ p143) ∨ (¬ p1273) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p121) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p143 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17432 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u0)

theorem step31028 (p10 p101 p141 p189 p193 p258 p288 p323 : Prop)
    (h26855 : p288 ∨ p258)
    (h26861 : p323 ∨ p10)
    (h26845 : p193 ∨ p189)
    (h17795 : (¬ p101) ∨ (¬ p141) ∨ (¬ p193) ∨ (¬ p288) ∨ (¬ p323)) : (¬ p101) ∨ p258 ∨ p10 ∨ (¬ p141) ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p258) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17795 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)

theorem step31030 (p17 p101 p102 p185 p255 p256 : Prop)
    (h26837 : p102 ∨ p101)
    (h26853 : p256 ∨ p17)
    (h22743 : (¬ p185) ∨ (¬ p255) ∨ (¬ p102) ∨ (¬ p256)) : (¬ p185) ∨ (¬ p255) ∨ p101 ∨ p17 := by
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
  rcases h22743 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step31032 (p101 p102 p283 p1076 p1077 p1115 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26837 : p102 ∨ p101)
    (h22746 : (¬ p1115) ∨ (¬ p102) ∨ (¬ p283) ∨ (¬ p1077)) : (¬ p1115) ∨ p1076 ∨ p101 ∨ (¬ p283) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p283 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h22746 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step31033 (p126 p301 p303 p329 p419 p996 : Prop)
    (h26857 : p301 ∨ p126)
    (h26905 : p996 ∨ p419)
    (h22747 : (¬ p996) ∨ (¬ p301) ∨ (¬ p329) ∨ (¬ p303)) : p126 ∨ p419 ∨ (¬ p329) ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p419) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p329 := by
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
  have u5 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h22747 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)

theorem step31034 (p10 p323 p364 p382 p406 p514 p789 p858 : Prop)
    (h26897 : p858 ∨ p789)
    (h26869 : p406 ∨ p382)
    (h26861 : p323 ∨ p10)
    (h22749 : (¬ p514) ∨ (¬ p364) ∨ (¬ p858) ∨ (¬ p323) ∨ (¬ p406)) : (¬ p514) ∨ (¬ p364) ∨ p789 ∨ p382 ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p514 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p364 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h22749 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u6)

theorem step31035 (p101 p102 p283 p756 p1584 : Prop)
    (h26837 : p102 ∨ p101)
    (h22750 : (¬ p1584) ∨ (¬ p756) ∨ (¬ p102) ∨ (¬ p283)) : (¬ p756) ∨ p101 ∨ (¬ p283) ∨ (¬ p1584) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p101) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p283 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h22750 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)

theorem step31036 (p10 p323 p364 p576 p581 p819 p1385 : Prop)
    (h26861 : p323 ∨ p10)
    (h26879 : p581 ∨ p576)
    (h22751 : (¬ p364) ∨ (¬ p581) ∨ (¬ p1385) ∨ (¬ p819) ∨ (¬ p323)) : (¬ p819) ∨ (¬ p364) ∨ p10 ∨ (¬ p1385) ∨ p576 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p819 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p364 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h22751 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)

theorem step31037 (p1 p108 p126 p301 p438 p1366 : Prop)
    (h26857 : p301 ∨ p126)
    (h22752 : (¬ p301) ∨ (¬ p438) ∨ (¬ p1) ∨ (¬ p108) ∨ (¬ p1366)) : (¬ p1366) ∨ p126 ∨ (¬ p1) ∨ (¬ p438) ∨ (¬ p108) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h22752 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u0)

theorem step31038 (p8 p101 p102 p283 p306 p836 : Prop)
    (h26837 : p102 ∨ p101)
    (h22753 : (¬ p8) ∨ (¬ p836) ∨ (¬ p102) ∨ (¬ p306) ∨ (¬ p283)) : (¬ p8) ∨ (¬ p306) ∨ (¬ p283) ∨ p101 ∨ (¬ p836) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p283 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h22753 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)

theorem step31041 (p89 p101 p102 p124 p304 p576 p581 p790 p1385 : Prop)
    (h26859 : p304 ∨ p124)
    (h26837 : p102 ∨ p101)
    (h26879 : p581 ∨ p576)
    (h26064 : (¬ p581) ∨ (¬ p790) ∨ (¬ p1385) ∨ (¬ p102) ∨ (¬ p89) ∨ (¬ p304)) : p124 ∨ p101 ∨ (¬ p790) ∨ p576 ∨ (¬ p1385) ∨ (¬ p89) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p101) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h26064 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)

theorem step31042 (p124 p138 p189 p193 p258 p261 p288 p304 : Prop)
    (h26859 : p304 ∨ p124)
    (h26855 : p288 ∨ p258)
    (h26845 : p193 ∨ p189)
    (h17244 : (¬ p138) ∨ (¬ p193) ∨ (¬ p261) ∨ (¬ p288) ∨ (¬ p304)) : (¬ p261) ∨ p124 ∨ (¬ p138) ∨ p258 ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17244 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step31043 (p17 p138 p185 p237 p419 p545 p789 p797 p836 p840 p858 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h26851 : p237 ∨ p185)
    (h26895 : p840 ∨ p836)
    (h26897 : p858 ∨ p789)
    (h17484 : (¬ p17) ∨ (¬ p138) ∨ (¬ p237) ∨ (¬ p545) ∨ (¬ p797) ∨ (¬ p840) ∨ (¬ p858) ∨ (¬ p996)) : (¬ p797) ∨ (¬ p545) ∨ p419 ∨ p185 ∨ p836 ∨ p789 ∨ (¬ p138) ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p797 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17484 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)
  · exact False.elim (q7 u8)

theorem step31047 (p125 p138 p185 p189 p193 p262 p303 p362 p387 p836 p1325 p1333 : Prop)
    (h26867 : p387 ∨ p303)
    (h26845 : p193 ∨ p189)
    (h26865 : p362 ∨ p125)
    (h26931 : p1333 ∨ p1325)
    (h17649 : (¬ p138) ∨ (¬ p185) ∨ (¬ p193) ∨ (¬ p262) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p836) ∨ (¬ p1333)) : (¬ p836) ∨ p303 ∨ (¬ p185) ∨ p189 ∨ p125 ∨ (¬ p138) ∨ p1325 ∨ (¬ p262) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h17649 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u11)

theorem step31049 (p125 p138 p189 p193 p262 p362 p434 p789 p790 p814 p858 : Prop)
    (h26893 : p814 ∨ p790)
    (h26845 : p193 ∨ p189)
    (h26897 : p858 ∨ p789)
    (h26865 : p362 ∨ p125)
    (h26065 : (¬ p858) ∨ (¬ p193) ∨ (¬ p814) ∨ (¬ p434) ∨ (¬ p138) ∨ (¬ p262) ∨ (¬ p362)) : (¬ p434) ∨ p790 ∨ p189 ∨ p789 ∨ p125 ∨ (¬ p262) ∨ (¬ p138) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p790) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h26065 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u10)

theorem step31050 (p11 p138 p189 p193 p261 p961 p1443 : Prop)
    (h26935 : p1443 ∨ p11)
    (h26845 : p193 ∨ p189)
    (h18419 : (¬ p138) ∨ (¬ p193) ∨ (¬ p261) ∨ (¬ p961) ∨ (¬ p1443)) : (¬ p961) ∨ (¬ p261) ∨ (¬ p138) ∨ p11 ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18419 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)

theorem step31051 (p126 p138 p189 p193 p515 p790 p814 : Prop)
    (h26893 : p814 ∨ p790)
    (h26845 : p193 ∨ p189)
    (h18827 : (¬ p126) ∨ (¬ p138) ∨ (¬ p193) ∨ (¬ p515) ∨ (¬ p814)) : (¬ p515) ∨ p790 ∨ p189 ∨ (¬ p138) ∨ (¬ p126) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p515 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p790) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18827 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)

theorem step31052 (p3 p12 p17 p138 p192 p226 p980 p1036 p1512 p1758 : Prop)
    (h26847 : p226 ∨ p3)
    (h26907 : p1036 ∨ p12)
    (h18973 : (¬ p17) ∨ (¬ p138) ∨ (¬ p192) ∨ (¬ p226) ∨ (¬ p980) ∨ (¬ p1036) ∨ (¬ p1512) ∨ (¬ p1758)) : (¬ p1512) ∨ (¬ p1758) ∨ (¬ p17) ∨ (¬ p192) ∨ (¬ p980) ∨ (¬ p138) ∨ p3 ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1512 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1758 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h18973 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u1)

theorem step31053 (p124 p138 p185 p189 p193 p262 p668 p836 p1076 p1077 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26845 : p193 ∨ p189)
    (h19490 : (¬ p124) ∨ (¬ p138) ∨ (¬ p185) ∨ (¬ p193) ∨ (¬ p262) ∨ (¬ p668) ∨ (¬ p836) ∨ (¬ p1077)) : (¬ p836) ∨ p1076 ∨ (¬ p138) ∨ (¬ p262) ∨ (¬ p185) ∨ p189 ∨ (¬ p124) ∨ (¬ p668) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19490 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u8)

theorem step31054 (p138 p166 p185 p189 p193 p225 p262 p303 p347 p368 p382 p406 : Prop)
    (h26869 : p406 ∨ p382)
    (h26845 : p193 ∨ p189)
    (h19853 : (¬ p138) ∨ (¬ p166) ∨ (¬ p185) ∨ (¬ p193) ∨ (¬ p225) ∨ (¬ p262) ∨ (¬ p303) ∨ (¬ p347) ∨ (¬ p368) ∨ (¬ p406)) : (¬ p185) ∨ p382 ∨ (¬ p347) ∨ (¬ p225) ∨ (¬ p303) ∨ (¬ p138) ∨ (¬ p262) ∨ (¬ p368) ∨ p189 ∨ (¬ p166) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p166 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u11 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h19853 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u2)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u10)

theorem step31056 (p41 p138 p262 p368 p382 p406 p1287 p1387 : Prop)
    (h26869 : p406 ∨ p382)
    (h20611 : (¬ p41) ∨ (¬ p138) ∨ (¬ p262) ∨ (¬ p368) ∨ (¬ p406) ∨ (¬ p1287) ∨ (¬ p1387)) : p382 ∨ (¬ p41) ∨ (¬ p1287) ∨ (¬ p138) ∨ (¬ p262) ∨ (¬ p1387) ∨ (¬ p368) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h20611 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u5)

theorem step31057 (p3 p14 p48 p138 p192 p226 p576 : Prop)
    (h26847 : p226 ∨ p3)
    (h17272 : (¬ p14) ∨ (¬ p48) ∨ (¬ p138) ∨ (¬ p192) ∨ (¬ p226) ∨ (¬ p576)) : p3 ∨ (¬ p192) ∨ (¬ p138) ∨ (¬ p14) ∨ (¬ p576) ∨ (¬ p48) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17272 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u4)

theorem step31058 (p3 p14 p17 p138 p192 p226 p234 p790 p800 p1187 : Prop)
    (h26847 : p226 ∨ p3)
    (h26921 : p1187 ∨ p234)
    (h18954 : (¬ p14) ∨ (¬ p17) ∨ (¬ p138) ∨ (¬ p192) ∨ (¬ p226) ∨ (¬ p790) ∨ (¬ p800) ∨ (¬ p1187)) : (¬ p800) ∨ p3 ∨ (¬ p790) ∨ (¬ p192) ∨ (¬ p138) ∨ p234 ∨ (¬ p14) ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p800 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p234) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18954 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u9)

theorem step31061 (p17 p47 p138 p382 p406 p820 p879 p898 p1287 : Prop)
    (h26869 : p406 ∨ p382)
    (h19766 : (¬ p17) ∨ (¬ p47) ∨ (¬ p138) ∨ (¬ p406) ∨ (¬ p820) ∨ (¬ p879) ∨ (¬ p898) ∨ (¬ p1287)) : p382 ∨ (¬ p820) ∨ (¬ p47) ∨ (¬ p138) ∨ (¬ p879) ∨ (¬ p17) ∨ (¬ p1287) ∨ (¬ p898) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p820 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p879 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p898 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19766 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u6)

theorem step31062 (p125 p126 p138 p189 p193 p261 : Prop)
    (h26845 : p193 ∨ p189)
    (h17173 : (¬ p125) ∨ (¬ p126) ∨ (¬ p138) ∨ (¬ p193) ∨ (¬ p261)) : (¬ p125) ∨ p189 ∨ (¬ p126) ∨ (¬ p138) ∨ (¬ p261) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17173 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)

theorem step31063 (p3 p17 p138 p163 p167 p186 : Prop)
    (h26843 : p167 ∨ p163)
    (h17177 : (¬ p3) ∨ (¬ p17) ∨ (¬ p138) ∨ (¬ p167) ∨ (¬ p186)) : (¬ p3) ∨ p163 ∨ (¬ p186) ∨ (¬ p138) ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17177 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)

theorem step31064 (p135 p258 p288 : Prop)
    (h26855 : p288 ∨ p258)
    (h18546 : p135 ∨ (¬ p288)) : p135 ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p135) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p258) := fun hu => hn (Or.inr hu)
  have u2 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18546 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)

theorem step31065 (p135 p189 p193 : Prop)
    (h26845 : p193 ∨ p189)
    (h20353 : p135 ∨ (¬ p193)) : p135 ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p135) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr hu)
  have u2 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20353 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)

theorem step31066 (p106 p163 p344 p424 p480 p656 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h17047 : (¬ p106) ∨ (¬ p163) ∨ (¬ p344) ∨ (¬ p480) ∨ (¬ p656) ∨ (¬ p796)) : p424 ∨ (¬ p163) ∨ (¬ p344) ∨ (¬ p106) ∨ (¬ p480) ∨ (¬ p656) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p480 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p656 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17047 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)

theorem step31069 (p106 p225 p348 p420 p601 p633 p636 : Prop)
    (h26885 : p636 ∨ p633)
    (h26881 : p601 ∨ p420)
    (h17758 : (¬ p106) ∨ (¬ p225) ∨ (¬ p348) ∨ (¬ p601) ∨ (¬ p636)) : p633 ∨ (¬ p106) ∨ p420 ∨ (¬ p348) ∨ (¬ p225) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17758 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step31070 (p12 p106 p980 p1036 p1083 p1452 : Prop)
    (h26907 : p1036 ∨ p12)
    (h19292 : (¬ p106) ∨ (¬ p980) ∨ (¬ p1036) ∨ (¬ p1083) ∨ (¬ p1452)) : (¬ p1083) ∨ (¬ p1452) ∨ (¬ p106) ∨ p12 ∨ (¬ p980) := by
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
  have u2 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19292 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)

theorem step31071 (p106 p163 p422 p1038 p1076 p1077 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h18762 : (¬ p106) ∨ (¬ p163) ∨ (¬ p422) ∨ (¬ p1038) ∨ (¬ p1077)) : (¬ p1038) ∨ (¬ p422) ∨ (¬ p106) ∨ p1076 ∨ (¬ p163) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1038 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18762 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)

theorem step31072 (p12 p106 p121 p124 p185 p227 p237 p304 p1036 p1115 p1116 p1206 : Prop)
    (h26859 : p304 ∨ p124)
    (h26907 : p1036 ∨ p12)
    (h26851 : p237 ∨ p185)
    (h26923 : p1206 ∨ p121)
    (h26915 : p1116 ∨ p1115)
    (h20530 : (¬ p106) ∨ (¬ p227) ∨ (¬ p237) ∨ (¬ p304) ∨ (¬ p1036) ∨ (¬ p1116) ∨ (¬ p1206)) : p124 ∨ p12 ∨ p185 ∨ p121 ∨ (¬ p106) ∨ p1115 ∨ (¬ p227) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p121) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20530 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u10)

theorem step31073 (p6 p10 p104 p127 p163 p167 p187 p323 p350 : Prop)
    (h26839 : p127 ∨ p6)
    (h26861 : p323 ∨ p10)
    (h26843 : p167 ∨ p163)
    (h19089 : (¬ p104) ∨ (¬ p127) ∨ (¬ p167) ∨ (¬ p187) ∨ (¬ p323) ∨ (¬ p350)) : (¬ p187) ∨ (¬ p104) ∨ p6 ∨ p10 ∨ (¬ p350) ∨ p163 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19089 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u4)

theorem step31074 (p6 p10 p14 p68 p104 p127 p229 p323 p350 : Prop)
    (h26849 : p229 ∨ p14)
    (h26861 : p323 ∨ p10)
    (h26839 : p127 ∨ p6)
    (h17672 : (¬ p68) ∨ (¬ p104) ∨ (¬ p127) ∨ (¬ p229) ∨ (¬ p323) ∨ (¬ p350)) : p14 ∨ (¬ p104) ∨ (¬ p68) ∨ p10 ∨ p6 ∨ (¬ p350) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17672 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u5)

theorem step31075 (p14 p18 p19 p104 p125 p207 p229 p350 p362 : Prop)
    (h26849 : p229 ∨ p14)
    (h26865 : p362 ∨ p125)
    (h26829 : p19 ∨ p18)
    (h16909 : (¬ p19) ∨ (¬ p104) ∨ (¬ p207) ∨ (¬ p229) ∨ (¬ p350) ∨ (¬ p362)) : p14 ∨ (¬ p104) ∨ (¬ p207) ∨ p125 ∨ (¬ p350) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h16909 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u7)

theorem step31080 (p88 p185 p918 p928 : Prop)
    (h26901 : p928 ∨ p918)
    (h12082 : (¬ p88) ∨ (¬ p185) ∨ (¬ p928)) : p918 ∨ (¬ p185) ∨ (¬ p88) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p918) := fun hu => hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h12082 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)

theorem step31082 (p3 p88 p163 p188 p226 p303 p387 p424 p438 p577 p600 p796 p1542 : Prop)
    (h26891 : p796 ∨ p424)
    (h26867 : p387 ∨ p303)
    (h26847 : p226 ∨ p3)
    (h18139 : (¬ p88) ∨ (¬ p163) ∨ (¬ p188) ∨ (¬ p226) ∨ (¬ p387) ∨ (¬ p438) ∨ (¬ p577) ∨ (¬ p600) ∨ (¬ p796) ∨ (¬ p1542)) : p424 ∨ (¬ p1542) ∨ (¬ p88) ∨ (¬ p438) ∨ (¬ p163) ∨ (¬ p577) ∨ (¬ p188) ∨ p303 ∨ (¬ p600) ∨ p3 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p600 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u11 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u12 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h18139 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u12)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u10)
  · exact False.elim (q9 u1)

theorem step31085 (p2 p88 p188 p303 p387 p419 p595 p599 p924 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26867 : p387 ∨ p303)
    (h19785 : (¬ p2) ∨ (¬ p88) ∨ (¬ p188) ∨ (¬ p387) ∨ (¬ p419) ∨ (¬ p595) ∨ (¬ p599) ∨ (¬ p924) ∨ (¬ p1099)) : (¬ p2) ∨ (¬ p88) ∨ p1096 ∨ (¬ p595) ∨ p303 ∨ (¬ p188) ∨ (¬ p599) ∨ (¬ p419) ∨ (¬ p924) := by
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
  have u2 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p599 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19785 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u9)

theorem step31086 (p88 p189 p224 p422 p657 p734 p903 p924 p1465 p1542 : Prop)
    (h26887 : p657 ∨ p224)
    (h19804 : (¬ p88) ∨ (¬ p189) ∨ (¬ p422) ∨ (¬ p657) ∨ (¬ p734) ∨ (¬ p903) ∨ (¬ p924) ∨ (¬ p1465) ∨ (¬ p1542)) : (¬ p1542) ∨ (¬ p422) ∨ (¬ p924) ∨ p224 ∨ (¬ p903) ∨ (¬ p189) ∨ (¬ p1465) ∨ (¬ p734) ∨ (¬ p88) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p903 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19804 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u0)

theorem step31087 (p88 p134 p188 p303 p382 p406 p422 p495 p577 p620 p1140 p1159 p1256 : Prop)
    (h26869 : p406 ∨ p382)
    (h26929 : p1256 ∨ p422)
    (h26919 : p1159 ∨ p1140)
    (h19809 : (¬ p88) ∨ (¬ p134) ∨ (¬ p188) ∨ (¬ p303) ∨ (¬ p406) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p620) ∨ (¬ p1159) ∨ (¬ p1256)) : p382 ∨ (¬ p620) ∨ (¬ p577) ∨ (¬ p88) ∨ p422 ∨ (¬ p495) ∨ (¬ p303) ∨ (¬ p134) ∨ (¬ p188) ∨ p1140 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p620 := by
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
  have u4 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u11 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u12 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h19809 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u12)
  · exact False.elim (q9 u11)

theorem step31089 (p88 p189 p419 p424 p796 p924 p1096 p1099 p1229 p1291 : Prop)
    (h26891 : p796 ∨ p424)
    (h26913 : p1099 ∨ p1096)
    (h20009 : (¬ p88) ∨ (¬ p189) ∨ (¬ p419) ∨ (¬ p796) ∨ (¬ p924) ∨ (¬ p1099) ∨ (¬ p1229) ∨ (¬ p1291)) : p424 ∨ (¬ p189) ∨ p1096 ∨ (¬ p419) ∨ (¬ p924) ∨ (¬ p88) ∨ (¬ p1229) ∨ (¬ p1291) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p88 := by
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
  have u8 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20009 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u7)

theorem step31090 (p88 p140 p189 p283 p918 p928 p1689 p1711 : Prop)
    (h26901 : p928 ∨ p918)
    (h20043 : (¬ p88) ∨ (¬ p140) ∨ (¬ p189) ∨ (¬ p283) ∨ (¬ p928) ∨ (¬ p1689) ∨ (¬ p1711)) : (¬ p1689) ∨ (¬ p1711) ∨ (¬ p140) ∨ (¬ p189) ∨ (¬ p88) ∨ (¬ p283) ∨ p918 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1689 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1711 := by
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
  have u4 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p283 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20043 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u1)

theorem step31091 (p88 p185 p434 p576 p581 p668 p690 p709 p836 p1055 p1061 : Prop)
    (h26879 : p581 ∨ p576)
    (h26909 : p1061 ∨ p1055)
    (h20522 : (¬ p88) ∨ (¬ p185) ∨ (¬ p434) ∨ (¬ p581) ∨ (¬ p668) ∨ (¬ p690) ∨ (¬ p709) ∨ (¬ p836) ∨ (¬ p1061)) : (¬ p690) ∨ (¬ p434) ∨ (¬ p709) ∨ (¬ p836) ∨ (¬ p185) ∨ (¬ p88) ∨ p576 ∨ (¬ p668) ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p709 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p836 := by
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
  have u6 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h20522 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u3)
  · exact False.elim (q8 u10)

theorem step31093 (p39 p68 p88 p185 p211 p368 p382 p406 p419 p739 p1366 p1584 : Prop)
    (h26869 : p406 ∨ p382)
    (h17783 : (¬ p39) ∨ (¬ p68) ∨ (¬ p88) ∨ (¬ p185) ∨ (¬ p211) ∨ (¬ p368) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p739) ∨ (¬ p1366) ∨ (¬ p1584)) : (¬ p739) ∨ (¬ p1366) ∨ p382 ∨ (¬ p368) ∨ (¬ p419) ∨ (¬ p39) ∨ (¬ p1584) ∨ (¬ p68) ∨ (¬ p185) ∨ (¬ p211) ∨ (¬ p88) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p739 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17783 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u11)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u0)
  · exact False.elim (q9 u1)
  · exact False.elim (q10 u6)

theorem step31094 (p15 p39 p69 p88 p690 p789 p815 p858 p1022 p1229 p1291 : Prop)
    (h26833 : p69 ∨ p15)
    (h26897 : p858 ∨ p789)
    (h19033 : (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p690) ∨ (¬ p815) ∨ (¬ p858) ∨ (¬ p1022) ∨ (¬ p1229) ∨ (¬ p1291)) : (¬ p1229) ∨ p15 ∨ (¬ p690) ∨ p789 ∨ (¬ p1022) ∨ (¬ p88) ∨ (¬ p1291) ∨ (¬ p39) ∨ (¬ p815) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1291 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p815 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19033 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u0)
  · exact False.elim (q8 u6)

theorem step31095 (p15 p39 p69 p88 p185 p224 p836 p1229 p1291 : Prop)
    (h26833 : p69 ∨ p15)
    (h19034 : (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p185) ∨ (¬ p224) ∨ (¬ p836) ∨ (¬ p1229) ∨ (¬ p1291)) : (¬ p836) ∨ (¬ p224) ∨ (¬ p1291) ∨ p15 ∨ (¬ p1229) ∨ (¬ p39) ∨ (¬ p185) ∨ (¬ p88) := by
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
  have u2 : p1291 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19034 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u2)

theorem step31096 (p15 p39 p69 p88 p185 p347 p420 p495 p499 p601 p836 : Prop)
    (h26875 : p499 ∨ p495)
    (h26833 : p69 ∨ p15)
    (h26881 : p601 ∨ p420)
    (h19036 : (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p185) ∨ (¬ p347) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p836)) : (¬ p836) ∨ p495 ∨ (¬ p185) ∨ (¬ p88) ∨ p15 ∨ (¬ p39) ∨ p420 ∨ (¬ p347) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19036 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u0)

theorem step31097 (p15 p39 p69 p88 p106 p185 p344 p836 p883 p1096 : Prop)
    (h26833 : p69 ∨ p15)
    (h20068 : (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p106) ∨ (¬ p185) ∨ (¬ p344) ∨ (¬ p836) ∨ (¬ p883) ∨ (¬ p1096)) : (¬ p1096) ∨ (¬ p836) ∨ (¬ p39) ∨ (¬ p883) ∨ (¬ p344) ∨ (¬ p88) ∨ (¬ p106) ∨ p15 ∨ (¬ p185) := by
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
  have u2 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p883 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h20068 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u3)
  · exact False.elim (q8 u0)

theorem step31098 (p15 p39 p69 p88 p185 p668 p836 p1095 p1096 : Prop)
    (h26833 : p69 ∨ p15)
    (h20481 : (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p185) ∨ (¬ p668) ∨ (¬ p836) ∨ (¬ p1095) ∨ (¬ p1096)) : (¬ p1096) ∨ p15 ∨ (¬ p88) ∨ (¬ p836) ∨ (¬ p1095) ∨ (¬ p39) ∨ (¬ p668) ∨ (¬ p185) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20481 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u0)

theorem step31099 (p39 p88 p124 p161 p224 p261 p304 p344 p346 p1000 p1146 p1225 p1465 : Prop)
    (h26859 : p304 ∨ p124)
    (h26925 : p1225 ∨ p161)
    (h26863 : p346 ∨ p344)
    (h20104 : (¬ p39) ∨ (¬ p88) ∨ (¬ p224) ∨ (¬ p261) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p1000) ∨ (¬ p1146) ∨ (¬ p1225) ∨ (¬ p1465)) : p124 ∨ p161 ∨ (¬ p224) ∨ (¬ p261) ∨ (¬ p1000) ∨ (¬ p1146) ∨ (¬ p88) ∨ (¬ p1465) ∨ (¬ p39) ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p161) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1146 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u11 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u12 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h20104 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u12)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u11)
  · exact False.elim (q9 u7)

theorem step31100 (p6 p39 p88 p124 p127 p224 p261 p304 p344 p346 p423 p1140 p1159 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26859 : p304 ∨ p124)
    (h26863 : p346 ∨ p344)
    (h26839 : p127 ∨ p6)
    (h20107 : (¬ p39) ∨ (¬ p88) ∨ (¬ p127) ∨ (¬ p224) ∨ (¬ p261) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p423) ∨ (¬ p1159)) : p1140 ∨ p124 ∨ (¬ p224) ∨ p344 ∨ (¬ p88) ∨ p6 ∨ (¬ p261) ∨ (¬ p39) ∨ (¬ p423) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u11 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u12 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20107 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u12)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u9)

theorem step31101 (p2 p11 p39 p68 p88 p124 p258 p261 p288 p304 p389 p419 p481 p996 : Prop)
    (h26859 : p304 ∨ p124)
    (h26873 : p481 ∨ p2)
    (h26905 : p996 ∨ p419)
    (h26855 : p288 ∨ p258)
    (h20455 : (¬ p11) ∨ (¬ p39) ∨ (¬ p68) ∨ (¬ p88) ∨ (¬ p261) ∨ (¬ p288) ∨ (¬ p304) ∨ (¬ p389) ∨ (¬ p481) ∨ (¬ p996)) : p124 ∨ (¬ p11) ∨ (¬ p88) ∨ p2 ∨ p419 ∨ (¬ p39) ∨ (¬ p389) ∨ (¬ p68) ∨ p258 ∨ (¬ p261) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u11 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u12 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u13 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h20455 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u13)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u11)
  · exact False.elim (q9 u12)

theorem step31102 (p17 p39 p88 p126 p301 p423 p438 p1035 p1335 : Prop)
    (h26857 : p301 ∨ p126)
    (h20059 : (¬ p17) ∨ (¬ p39) ∨ (¬ p88) ∨ (¬ p301) ∨ (¬ p423) ∨ (¬ p438) ∨ (¬ p1035) ∨ (¬ p1335)) : (¬ p1035) ∨ p126 ∨ (¬ p423) ∨ (¬ p39) ∨ (¬ p438) ∨ (¬ p1335) ∨ (¬ p88) ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20059 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u5)

theorem step31103 (p2 p17 p39 p68 p88 p258 p419 p481 p996 p1076 : Prop)
    (h26905 : p996 ∨ p419)
    (h26873 : p481 ∨ p2)
    (h26066 : (¬ p68) ∨ (¬ p39) ∨ (¬ p88) ∨ (¬ p17) ∨ (¬ p996) ∨ (¬ p258) ∨ (¬ p1076) ∨ (¬ p481)) : p419 ∨ (¬ p258) ∨ p2 ∨ (¬ p88) ∨ (¬ p1076) ∨ (¬ p17) ∨ (¬ p68) ∨ (¬ p39) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p39 := by
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
    · exact False.elim (u2 q1)
  rcases h26066 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u9)

theorem step31105 (p15 p39 p69 p88 p124 p126 p258 p261 p288 p301 p304 p595 p599 : Prop)
    (h26859 : p304 ∨ p124)
    (h26855 : p288 ∨ p258)
    (h26833 : p69 ∨ p15)
    (h26857 : p301 ∨ p126)
    (h20115 : (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p261) ∨ (¬ p288) ∨ (¬ p301) ∨ (¬ p304) ∨ (¬ p595) ∨ (¬ p599)) : p124 ∨ p258 ∨ p15 ∨ p126 ∨ (¬ p39) ∨ (¬ p261) ∨ (¬ p595) ∨ (¬ p599) ∨ (¬ p88) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p258) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p126) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p261 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u11 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u12 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20115 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u11)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u12)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step31107 (p15 p39 p69 p88 p124 p224 p261 p303 p304 p345 p595 p657 p901 : Prop)
    (h26859 : p304 ∨ p124)
    (h26833 : p69 ∨ p15)
    (h26887 : p657 ∨ p224)
    (h20109 : (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p261) ∨ (¬ p303) ∨ (¬ p304) ∨ (¬ p345) ∨ (¬ p595) ∨ (¬ p657) ∨ (¬ p901)) : p124 ∨ p15 ∨ (¬ p88) ∨ (¬ p901) ∨ (¬ p261) ∨ (¬ p303) ∨ (¬ p39) ∨ p224 ∨ (¬ p595) ∨ (¬ p345) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p901 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p345 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u11 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u12 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h20109 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u11)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u12)
  · exact False.elim (q9 u3)

theorem step31108 (p6 p10 p88 p188 p303 p665 p924 p1096 p1099 p1229 p1310 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h20368 : (¬ p6) ∨ (¬ p10) ∨ (¬ p88) ∨ (¬ p188) ∨ (¬ p303) ∨ (¬ p665) ∨ (¬ p924) ∨ (¬ p1099) ∨ (¬ p1229) ∨ (¬ p1310)) : (¬ p1229) ∨ p1096 ∨ (¬ p188) ∨ (¬ p665) ∨ (¬ p303) ∨ (¬ p924) ∨ (¬ p10) ∨ (¬ p1310) ∨ (¬ p6) ∨ (¬ p88) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20368 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u0)
  · exact False.elim (q9 u7)

theorem step31109 (p10 p88 p134 p189 p595 p599 p924 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h18943 : (¬ p10) ∨ (¬ p88) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p595) ∨ (¬ p599) ∨ (¬ p924) ∨ (¬ p1099)) : (¬ p10) ∨ (¬ p599) ∨ (¬ p924) ∨ (¬ p595) ∨ (¬ p88) ∨ p1096 ∨ (¬ p189) ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p599 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18943 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u8)

theorem step31110 (p17 p88 p258 p595 p616 p1076 p1229 p1309 p1389 : Prop)
    (h26883 : p616 ∨ p595)
    (h19523 : (¬ p17) ∨ (¬ p88) ∨ (¬ p258) ∨ (¬ p616) ∨ (¬ p1076) ∨ (¬ p1229) ∨ (¬ p1309) ∨ (¬ p1389)) : (¬ p1389) ∨ (¬ p258) ∨ (¬ p1076) ∨ (¬ p1309) ∨ (¬ p1229) ∨ (¬ p88) ∨ (¬ p17) ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h19523 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u0)

theorem step31111 (p6 p41 p87 p121 p127 p187 p228 p789 p790 p814 p858 : Prop)
    (h26893 : p814 ∨ p790)
    (h26839 : p127 ∨ p6)
    (h26897 : p858 ∨ p789)
    (h16297 : (¬ p41) ∨ (¬ p87) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p187) ∨ (¬ p228) ∨ (¬ p814) ∨ (¬ p858)) : p790 ∨ p6 ∨ (¬ p187) ∨ (¬ p87) ∨ (¬ p121) ∨ (¬ p41) ∨ (¬ p228) ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p790) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h16297 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u10)

theorem step31113 (p3 p41 p87 p163 p188 p226 : Prop)
    (h26847 : p226 ∨ p3)
    (h19279 : (¬ p41) ∨ (¬ p87) ∨ (¬ p163) ∨ (¬ p188) ∨ (¬ p226)) : p3 ∨ (¬ p41) ∨ (¬ p163) ∨ (¬ p87) ∨ (¬ p188) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19279 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)

theorem step31114 (p17 p87 p158 p303 p420 p579 p665 p918 p928 p1055 p1061 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h26901 : p928 ∨ p918)
    (h19591 : (¬ p17) ∨ (¬ p87) ∨ (¬ p158) ∨ (¬ p303) ∨ (¬ p420) ∨ (¬ p579) ∨ (¬ p665) ∨ (¬ p928) ∨ (¬ p1061)) : (¬ p420) ∨ p1055 ∨ (¬ p579) ∨ (¬ p87) ∨ p918 ∨ (¬ p303) ∨ (¬ p158) ∨ (¬ p17) ∨ (¬ p665) := by
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
  have u3 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19591 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u9)

theorem step31115 (p6 p41 p87 p101 p102 p127 p185 p187 p224 p897 p926 : Prop)
    (h26839 : p127 ∨ p6)
    (h26837 : p102 ∨ p101)
    (h19630 : (¬ p41) ∨ (¬ p87) ∨ (¬ p102) ∨ (¬ p127) ∨ (¬ p185) ∨ (¬ p187) ∨ (¬ p224) ∨ (¬ p897) ∨ (¬ p926)) : (¬ p185) ∨ p6 ∨ p101 ∨ (¬ p41) ∨ (¬ p187) ∨ (¬ p926) ∨ (¬ p224) ∨ (¬ p87) ∨ (¬ p897) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p185 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p926 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19630 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u5)

theorem step31116 (p17 p87 p158 p224 p351 p382 p406 p420 p579 p680 p918 p928 : Prop)
    (h26869 : p406 ∨ p382)
    (h26901 : p928 ∨ p918)
    (h20189 : (¬ p17) ∨ (¬ p87) ∨ (¬ p158) ∨ (¬ p224) ∨ (¬ p351) ∨ (¬ p406) ∨ (¬ p420) ∨ (¬ p579) ∨ (¬ p680) ∨ (¬ p928)) : p382 ∨ (¬ p420) ∨ (¬ p17) ∨ (¬ p158) ∨ (¬ p87) ∨ (¬ p680) ∨ p918 ∨ (¬ p579) ∨ (¬ p351) ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p579 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u11 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20189 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u11)

theorem step31117 (p17 p87 p382 p406 p579 p633 p636 p816 p1076 p1385 p1393 : Prop)
    (h26885 : p636 ∨ p633)
    (h26933 : p1393 ∨ p1385)
    (h26869 : p406 ∨ p382)
    (h26067 : (¬ p579) ∨ (¬ p1393) ∨ (¬ p87) ∨ (¬ p816) ∨ (¬ p1076) ∨ (¬ p17) ∨ (¬ p406) ∨ (¬ p636)) : (¬ p579) ∨ p633 ∨ (¬ p17) ∨ (¬ p87) ∨ (¬ p816) ∨ p1385 ∨ p382 ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p579 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p633) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p816 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h26067 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u8)

theorem step31118 (p8 p17 p87 p106 p158 p225 p579 p633 p636 p918 p928 : Prop)
    (h26885 : p636 ∨ p633)
    (h26901 : p928 ∨ p918)
    (h19094 : (¬ p8) ∨ (¬ p17) ∨ (¬ p87) ∨ (¬ p106) ∨ (¬ p158) ∨ (¬ p225) ∨ (¬ p579) ∨ (¬ p636) ∨ (¬ p928)) : p633 ∨ (¬ p579) ∨ (¬ p17) ∨ (¬ p158) ∨ (¬ p8) ∨ (¬ p225) ∨ p918 ∨ (¬ p87) ∨ (¬ p106) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : p579 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19094 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u10)

theorem step31119 (p8 p17 p87 p158 p224 p389 p455 p456 p579 p657 p918 p928 : Prop)
    (h26871 : p456 ∨ p455)
    (h26887 : p657 ∨ p224)
    (h26901 : p928 ∨ p918)
    (h20191 : (¬ p8) ∨ (¬ p17) ∨ (¬ p87) ∨ (¬ p158) ∨ (¬ p389) ∨ (¬ p456) ∨ (¬ p579) ∨ (¬ p657) ∨ (¬ p928)) : p455 ∨ (¬ p579) ∨ (¬ p8) ∨ p224 ∨ (¬ p87) ∨ (¬ p389) ∨ p918 ∨ (¬ p17) ∨ (¬ p158) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : p579 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20191 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u11)

theorem step31120 (p41 p87 p187 p1000 p1140 p1325 p1333 p1349 p1489 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h18789 : (¬ p41) ∨ (¬ p87) ∨ (¬ p187) ∨ (¬ p1000) ∨ (¬ p1140) ∨ (¬ p1333) ∨ (¬ p1349) ∨ (¬ p1489)) : (¬ p41) ∨ (¬ p1349) ∨ (¬ p1489) ∨ p1325 ∨ (¬ p187) ∨ (¬ p1140) ∨ (¬ p87) ∨ (¬ p1000) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18789 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u2)

theorem step31121 (p41 p87 p188 p422 p1140 p1159 p1256 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26929 : p1256 ∨ p422)
    (h16904 : (¬ p41) ∨ (¬ p87) ∨ (¬ p188) ∨ (¬ p1159) ∨ (¬ p1256)) : p1140 ∨ (¬ p41) ∨ p422 ∨ (¬ p87) ∨ (¬ p188) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p188 := by
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
  rcases h16904 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)

theorem step31122 (p87 p185 p419 p542 p789 p897 p926 p1385 p1393 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h17688 : (¬ p87) ∨ (¬ p185) ∨ (¬ p419) ∨ (¬ p542) ∨ (¬ p789) ∨ (¬ p897) ∨ (¬ p926) ∨ (¬ p1393)) : (¬ p789) ∨ p1385 ∨ (¬ p926) ∨ (¬ p419) ∨ (¬ p542) ∨ (¬ p185) ∨ (¬ p87) ∨ (¬ p897) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1385) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p926 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17688 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u8)

theorem step31123 (p87 p185 p224 p227 p228 p262 p576 p581 p836 : Prop)
    (h26879 : p581 ∨ p576)
    (h19925 : (¬ p87) ∨ (¬ p185) ∨ (¬ p224) ∨ (¬ p227) ∨ (¬ p228) ∨ (¬ p262) ∨ (¬ p581) ∨ (¬ p836)) : (¬ p836) ∨ p576 ∨ (¬ p224) ∨ (¬ p87) ∨ (¬ p228) ∨ (¬ p227) ∨ (¬ p262) ∨ (¬ p185) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19925 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u0)

theorem step31125 (p87 p124 p262 p576 p581 p665 p789 p790 p814 p858 p1076 p1077 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26879 : p581 ∨ p576)
    (h26897 : p858 ∨ p789)
    (h26893 : p814 ∨ p790)
    (h16282 : (¬ p87) ∨ (¬ p124) ∨ (¬ p262) ∨ (¬ p581) ∨ (¬ p665) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1077)) : p1076 ∨ p576 ∨ (¬ p665) ∨ p789 ∨ (¬ p124) ∨ (¬ p87) ∨ p790 ∨ (¬ p262) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1076) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h16282 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u8)

theorem step31126 (p87 p125 p185 p262 p303 p362 p387 p576 p581 p1115 : Prop)
    (h26879 : p581 ∨ p576)
    (h26865 : p362 ∨ p125)
    (h26867 : p387 ∨ p303)
    (h26068 : (¬ p581) ∨ (¬ p1115) ∨ (¬ p87) ∨ (¬ p387) ∨ (¬ p185) ∨ (¬ p362) ∨ (¬ p262)) : (¬ p1115) ∨ p576 ∨ (¬ p87) ∨ p125 ∨ (¬ p262) ∨ (¬ p185) ∨ p303 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h26068 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u4)

theorem step31127 (p87 p125 p185 p225 p262 p362 p434 p544 p576 p581 p836 : Prop)
    (h26879 : p581 ∨ p576)
    (h26877 : p544 ∨ p225)
    (h26865 : p362 ∨ p125)
    (h19476 : (¬ p87) ∨ (¬ p185) ∨ (¬ p262) ∨ (¬ p362) ∨ (¬ p434) ∨ (¬ p544) ∨ (¬ p581) ∨ (¬ p836)) : (¬ p434) ∨ (¬ p836) ∨ p576 ∨ (¬ p262) ∨ p225 ∨ (¬ p87) ∨ (¬ p185) ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h19476 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u1)

theorem step31128 (p87 p185 p262 p303 p347 p368 p382 p406 p576 p581 p897 p926 : Prop)
    (h26869 : p406 ∨ p382)
    (h26879 : p581 ∨ p576)
    (h19927 : (¬ p87) ∨ (¬ p185) ∨ (¬ p262) ∨ (¬ p303) ∨ (¬ p347) ∨ (¬ p368) ∨ (¬ p406) ∨ (¬ p581) ∨ (¬ p897) ∨ (¬ p926)) : p382 ∨ p576 ∨ (¬ p185) ∨ (¬ p926) ∨ (¬ p87) ∨ (¬ p897) ∨ (¬ p347) ∨ (¬ p368) ∨ (¬ p262) ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p926 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u11 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19927 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u11)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u3)

theorem step31129 (p2 p87 p158 p303 p327 p387 p481 p556 p789 p790 p814 p858 p918 p928 : Prop)
    (h26901 : p928 ∨ p918)
    (h26867 : p387 ∨ p303)
    (h26893 : p814 ∨ p790)
    (h26897 : p858 ∨ p789)
    (h26873 : p481 ∨ p2)
    (h19588 : (¬ p87) ∨ (¬ p158) ∨ (¬ p327) ∨ (¬ p387) ∨ (¬ p481) ∨ (¬ p556) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p928)) : (¬ p556) ∨ p918 ∨ (¬ p158) ∨ p303 ∨ (¬ p327) ∨ p790 ∨ (¬ p87) ∨ p789 ∨ p2 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p556 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p327 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u12 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u13 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h19588 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u13)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u11)
  · exact False.elim (q7 u12)
  · exact False.elim (q8 u9)

theorem step31130 (p87 p261 p576 p581 p1624 p1651 : Prop)
    (h26879 : p581 ∨ p576)
    (h18961 : (¬ p87) ∨ (¬ p261) ∨ (¬ p581) ∨ (¬ p1624) ∨ (¬ p1651)) : (¬ p1651) ∨ (¬ p1624) ∨ (¬ p261) ∨ (¬ p87) ∨ p576 := by
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
  have u2 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18961 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)

theorem step31131 (p87 p382 p519 p576 p581 p789 p815 : Prop)
    (h26879 : p581 ∨ p576)
    (h16280 : (¬ p87) ∨ (¬ p382) ∨ (¬ p519) ∨ (¬ p581) ∨ (¬ p789) ∨ (¬ p815)) : (¬ p789) ∨ p576 ∨ (¬ p382) ∨ (¬ p87) ∨ (¬ p519) ∨ (¬ p815) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p519 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p815 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16280 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u5)

theorem step31132 (p87 p125 p126 p261 p576 p581 : Prop)
    (h26879 : p581 ∨ p576)
    (h17664 : (¬ p87) ∨ (¬ p125) ∨ (¬ p126) ∨ (¬ p261) ∨ (¬ p581)) : p576 ∨ (¬ p125) ∨ (¬ p87) ∨ (¬ p126) ∨ (¬ p261) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p576) := fun hu => hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17664 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)

theorem step31134 (p3 p41 p87 p185 p187 p225 p544 p664 p1115 : Prop)
    (h26877 : p544 ∨ p225)
    (h19331 : (¬ p3) ∨ (¬ p41) ∨ (¬ p87) ∨ (¬ p185) ∨ (¬ p187) ∨ (¬ p544) ∨ (¬ p664) ∨ (¬ p1115)) : p225 ∨ (¬ p41) ∨ (¬ p1115) ∨ (¬ p187) ∨ (¬ p185) ∨ (¬ p3) ∨ (¬ p87) ∨ (¬ p664) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p225) := fun hu => hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19331 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u2)

theorem step31135 (p3 p41 p87 p106 p185 p187 p1076 p1077 p1115 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h19348 : (¬ p3) ∨ (¬ p41) ∨ (¬ p87) ∨ (¬ p106) ∨ (¬ p185) ∨ (¬ p187) ∨ (¬ p1077) ∨ (¬ p1115)) : (¬ p1115) ∨ p1076 ∨ (¬ p185) ∨ (¬ p187) ∨ (¬ p3) ∨ (¬ p106) ∨ (¬ p41) ∨ (¬ p87) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19348 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u0)

theorem step31136 (p87 p124 p258 p261 p288 p304 p576 p581 : Prop)
    (h26879 : p581 ∨ p576)
    (h26859 : p304 ∨ p124)
    (h26855 : p288 ∨ p258)
    (h19229 : (¬ p87) ∨ (¬ p261) ∨ (¬ p288) ∨ (¬ p304) ∨ (¬ p581)) : p576 ∨ p124 ∨ p258 ∨ (¬ p261) ∨ (¬ p87) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p576) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19229 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step31138 (p2 p17 p41 p87 p187 p389 p419 p455 p456 p481 p579 p996 : Prop)
    (h26871 : p456 ∨ p455)
    (h26905 : p996 ∨ p419)
    (h26873 : p481 ∨ p2)
    (h20237 : (¬ p17) ∨ (¬ p41) ∨ (¬ p87) ∨ (¬ p187) ∨ (¬ p389) ∨ (¬ p456) ∨ (¬ p481) ∨ (¬ p579) ∨ (¬ p996)) : (¬ p389) ∨ (¬ p579) ∨ (¬ p87) ∨ p455 ∨ (¬ p187) ∨ p419 ∨ p2 ∨ (¬ p41) ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p579 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p455) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u11 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20237 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u11)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u10)

theorem step31139 (p8 p87 p101 p121 p158 p224 p261 p657 p918 p928 p961 : Prop)
    (h26887 : p657 ∨ p224)
    (h26901 : p928 ∨ p918)
    (h19780 : (¬ p8) ∨ (¬ p87) ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p158) ∨ (¬ p261) ∨ (¬ p657) ∨ (¬ p928) ∨ (¬ p961)) : (¬ p101) ∨ (¬ p961) ∨ (¬ p261) ∨ (¬ p158) ∨ p224 ∨ (¬ p8) ∨ (¬ p121) ∨ p918 ∨ (¬ p87) := by
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
  have u2 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h19780 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u1)

theorem step31140 (p8 p87 p158 p189 p224 p422 p657 p918 p928 p1004 : Prop)
    (h26901 : p928 ∨ p918)
    (h26887 : p657 ∨ p224)
    (h19836 : (¬ p8) ∨ (¬ p87) ∨ (¬ p158) ∨ (¬ p189) ∨ (¬ p422) ∨ (¬ p657) ∨ (¬ p928) ∨ (¬ p1004)) : (¬ p422) ∨ (¬ p1004) ∨ (¬ p158) ∨ (¬ p8) ∨ (¬ p87) ∨ p918 ∨ p224 ∨ (¬ p189) := by
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
  have u2 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u9 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19836 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u1)

theorem step31141 (p87 p124 p185 p262 p344 p576 p581 p664 p1115 : Prop)
    (h26879 : p581 ∨ p576)
    (h16269 : (¬ p87) ∨ (¬ p124) ∨ (¬ p185) ∨ (¬ p262) ∨ (¬ p344) ∨ (¬ p581) ∨ (¬ p664) ∨ (¬ p1115)) : (¬ p1115) ∨ (¬ p344) ∨ (¬ p664) ∨ p576 ∨ (¬ p185) ∨ (¬ p124) ∨ (¬ p262) ∨ (¬ p87) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16269 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u0)

theorem step31142 (p87 p124 p185 p262 p576 p581 p668 p897 p926 p1076 p1077 : Prop)
    (h26879 : p581 ∨ p576)
    (h26911 : p1077 ∨ p1076)
    (h19424 : (¬ p87) ∨ (¬ p124) ∨ (¬ p185) ∨ (¬ p262) ∨ (¬ p581) ∨ (¬ p668) ∨ (¬ p897) ∨ (¬ p926) ∨ (¬ p1077)) : (¬ p926) ∨ p576 ∨ (¬ p262) ∨ (¬ p185) ∨ (¬ p87) ∨ p1076 ∨ (¬ p897) ∨ (¬ p668) ∨ (¬ p124) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p926 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19424 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u0)
  · exact False.elim (q8 u10)

theorem step31143 (p87 p382 p789 p815 p1385 p1393 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h19025 : (¬ p87) ∨ (¬ p382) ∨ (¬ p789) ∨ (¬ p815) ∨ (¬ p1393)) : (¬ p789) ∨ p1385 ∨ (¬ p87) ∨ (¬ p382) ∨ (¬ p815) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1385) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p815 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19025 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)

theorem step31144 (p8 p14 p47 p87 p110 p158 p189 p229 p344 p346 p918 p928 : Prop)
    (h26849 : p229 ∨ p14)
    (h26901 : p928 ∨ p918)
    (h26863 : p346 ∨ p344)
    (h17555 : (¬ p8) ∨ (¬ p47) ∨ (¬ p87) ∨ (¬ p110) ∨ (¬ p158) ∨ (¬ p189) ∨ (¬ p229) ∨ (¬ p346) ∨ (¬ p928)) : p14 ∨ p918 ∨ (¬ p189) ∨ p344 ∨ (¬ p158) ∨ (¬ p47) ∨ (¬ p87) ∨ (¬ p8) ∨ (¬ p110) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u11 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17555 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u11)
  · exact False.elim (q8 u10)

theorem step31146 (p84 p135 p185 p187 p419 p435 p475 p576 p581 p687 p836 p996 : Prop)
    (h26879 : p581 ∨ p576)
    (h26905 : p996 ∨ p419)
    (h20518 : p84 ∨ (¬ p135) ∨ (¬ p185) ∨ (¬ p187) ∨ (¬ p435) ∨ (¬ p475) ∨ (¬ p581) ∨ (¬ p687) ∨ (¬ p836) ∨ (¬ p996)) : p84 ∨ p576 ∨ (¬ p435) ∨ (¬ p475) ∨ (¬ p185) ∨ (¬ p687) ∨ (¬ p187) ∨ p419 ∨ (¬ p836) ∨ (¬ p135) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p84) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p475 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u11 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h20518 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u8)
  · exact False.elim (q9 u11)

theorem step31148 (p83 p136 p189 p455 p456 p1611 p1644 : Prop)
    (h26871 : p456 ∨ p455)
    (h18929 : (¬ p83) ∨ (¬ p136) ∨ (¬ p189) ∨ (¬ p456) ∨ (¬ p1611) ∨ (¬ p1644)) : (¬ p1611) ∨ p455 ∨ (¬ p1644) ∨ (¬ p189) ∨ (¬ p136) ∨ (¬ p83) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1611 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p455) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1644 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p136 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18929 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u2)

theorem step31149 (p10 p41 p83 p189 p323 p515 p1385 : Prop)
    (h26861 : p323 ∨ p10)
    (h19829 : (¬ p41) ∨ (¬ p83) ∨ (¬ p189) ∨ (¬ p323) ∨ (¬ p515) ∨ (¬ p1385)) : (¬ p515) ∨ (¬ p1385) ∨ (¬ p189) ∨ (¬ p41) ∨ p10 ∨ (¬ p83) := by
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
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19829 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u1)

theorem step31150 (p41 p83 p189 p224 p382 p406 p680 p842 p1385 : Prop)
    (h26869 : p406 ∨ p382)
    (h22759 : (¬ p680) ∨ (¬ p842) ∨ (¬ p189) ∨ (¬ p224) ∨ (¬ p83) ∨ (¬ p41) ∨ (¬ p406) ∨ (¬ p1385)) : p382 ∨ (¬ p41) ∨ (¬ p189) ∨ (¬ p1385) ∨ (¬ p842) ∨ (¬ p680) ∨ (¬ p83) ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p842 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h22759 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u3)

theorem step31151 (p17 p83 p224 p382 p406 p576 p581 p617 p842 p1385 : Prop)
    (h26869 : p406 ∨ p382)
    (h26879 : p581 ∨ p576)
    (h20200 : (¬ p17) ∨ (¬ p83) ∨ (¬ p224) ∨ (¬ p406) ∨ (¬ p581) ∨ (¬ p617) ∨ (¬ p842) ∨ (¬ p1385)) : p382 ∨ (¬ p224) ∨ (¬ p17) ∨ (¬ p83) ∨ p576 ∨ (¬ p1385) ∨ (¬ p617) ∨ (¬ p842) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p617 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p842 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20200 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u5)

theorem step31152 (p2 p17 p83 p424 p576 p581 p1140 p1249 p1258 : Prop)
    (h26879 : p581 ∨ p576)
    (h20205 : (¬ p2) ∨ (¬ p17) ∨ (¬ p83) ∨ (¬ p424) ∨ (¬ p581) ∨ (¬ p1140) ∨ (¬ p1249) ∨ (¬ p1258)) : (¬ p1258) ∨ (¬ p1249) ∨ (¬ p1140) ∨ (¬ p17) ∨ (¬ p83) ∨ (¬ p2) ∨ p576 ∨ (¬ p424) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1140 := by
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
  have u5 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20205 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u0)

theorem step31153 (p15 p49 p83 p185 p918 p928 : Prop)
    (h26901 : p928 ∨ p918)
    (h16329 : (¬ p15) ∨ (¬ p49) ∨ (¬ p83) ∨ (¬ p185) ∨ (¬ p928)) : (¬ p15) ∨ p918 ∨ (¬ p83) ∨ (¬ p185) ∨ (¬ p49) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16329 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)

theorem step31154 (p3 p14 p17 p83 p226 p420 p438 p579 p1370 p1805 : Prop)
    (h26847 : p226 ∨ p3)
    (h19267 : (¬ p14) ∨ (¬ p17) ∨ (¬ p83) ∨ (¬ p226) ∨ (¬ p420) ∨ (¬ p438) ∨ (¬ p579) ∨ (¬ p1370) ∨ (¬ p1805)) : (¬ p1805) ∨ (¬ p1370) ∨ (¬ p14) ∨ p3 ∨ (¬ p83) ∨ (¬ p438) ∨ (¬ p17) ∨ (¬ p579) ∨ (¬ p420) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1805 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1370 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p579 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19267 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u0)

theorem step31155 (p41 p45 p83 p134 p185 p918 p928 : Prop)
    (h26831 : p45 ∨ p41)
    (h26901 : p928 ∨ p918)
    (h19426 : (¬ p45) ∨ (¬ p83) ∨ (¬ p134) ∨ (¬ p185) ∨ (¬ p928)) : p41 ∨ p918 ∨ (¬ p185) ∨ (¬ p83) ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p41) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19426 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)

theorem step31156 (p16 p63 p83 p85 : Prop)
    (h26835 : p85 ∨ p63)
    (h17932 : p16 ∨ (¬ p83) ∨ (¬ p85)) : p16 ∨ (¬ p83) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p16) := fun hu => hn (Or.inl hu)
  have u1 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17932 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)

theorem step31157 (p41 p83 p189 p495 p499 p582 : Prop)
    (h26875 : p499 ∨ p495)
    (h16713 : (¬ p41) ∨ (¬ p83) ∨ (¬ p189) ∨ (¬ p499) ∨ (¬ p582)) : p495 ∨ (¬ p41) ∨ (¬ p189) ∨ (¬ p83) ∨ (¬ p582) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p495) := fun hu => hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h16713 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)

theorem step31158 (p83 p185 p303 p382 p406 p521 p617 p918 p928 p1385 : Prop)
    (h26869 : p406 ∨ p382)
    (h26901 : p928 ∨ p918)
    (h19898 : (¬ p83) ∨ (¬ p185) ∨ (¬ p303) ∨ (¬ p406) ∨ (¬ p521) ∨ (¬ p617) ∨ (¬ p928) ∨ (¬ p1385)) : p382 ∨ p918 ∨ (¬ p617) ∨ (¬ p1385) ∨ (¬ p521) ∨ (¬ p185) ∨ (¬ p303) ∨ (¬ p83) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p617 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p521 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19898 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u3)

theorem step31160 (p3 p72 p234 p382 p480 p880 p1076 p1095 p1187 p1325 : Prop)
    (h26921 : p1187 ∨ p234)
    (h17878 : (¬ p3) ∨ (¬ p72) ∨ (¬ p382) ∨ (¬ p480) ∨ (¬ p880) ∨ (¬ p1076) ∨ (¬ p1095) ∨ (¬ p1187) ∨ (¬ p1325)) : p234 ∨ (¬ p382) ∨ (¬ p1095) ∨ (¬ p3) ∨ (¬ p1325) ∨ (¬ p480) ∨ (¬ p880) ∨ (¬ p72) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p480 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p880 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17878 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u4)

theorem step31161 (p382 p406 p419 p444 p475 p495 p1366 p1604 : Prop)
    (h26869 : p406 ∨ p382)
    (h26071 : (¬ p1604) ∨ (¬ p495) ∨ (¬ p419) ∨ (¬ p1366) ∨ (¬ p444) ∨ (¬ p406) ∨ (¬ p475)) : (¬ p1604) ∨ (¬ p444) ∨ (¬ p1366) ∨ (¬ p419) ∨ (¬ p475) ∨ (¬ p495) ∨ p382 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1604 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p444 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
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
  have u6 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h26071 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u4)

theorem step31162 (p13 p455 p456 p495 p980 p1035 p1140 : Prop)
    (h26871 : p456 ∨ p455)
    (h26072 : (¬ p980) ∨ (¬ p13) ∨ (¬ p1140) ∨ (¬ p456) ∨ (¬ p1035) ∨ (¬ p495)) : p455 ∨ (¬ p1035) ∨ (¬ p495) ∨ (¬ p980) ∨ (¬ p13) ∨ (¬ p1140) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h26072 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)

theorem step31164 (p6 p121 p127 p224 p228 p897 p1096 p1099 : Prop)
    (h26839 : p127 ∨ p6)
    (h26913 : p1099 ∨ p1096)
    (h26074 : (¬ p1099) ∨ (¬ p228) ∨ (¬ p127) ∨ (¬ p224) ∨ (¬ p121) ∨ (¬ p897)) : (¬ p121) ∨ p6 ∨ (¬ p228) ∨ (¬ p897) ∨ p1096 ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p224 := by
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
    · exact False.elim (u4 q1)
  rcases h26074 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u3)

theorem step31165 (p6 p10 p127 p323 p521 p595 p616 p1022 p1545 : Prop)
    (h26839 : p127 ∨ p6)
    (h26861 : p323 ∨ p10)
    (h26883 : p616 ∨ p595)
    (h26075 : (¬ p1545) ∨ (¬ p616) ∨ (¬ p323) ∨ (¬ p127) ∨ (¬ p1022) ∨ (¬ p521)) : (¬ p1022) ∨ (¬ p1545) ∨ p6 ∨ (¬ p521) ∨ p10 ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p521 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u8 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26075 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u3)

theorem step31166 (p6 p10 p127 p224 p323 p347 p595 p616 p657 p1287 : Prop)
    (h26839 : p127 ∨ p6)
    (h26887 : p657 ∨ p224)
    (h26861 : p323 ∨ p10)
    (h26883 : p616 ∨ p595)
    (h26076 : (¬ p1287) ∨ (¬ p616) ∨ (¬ p347) ∨ (¬ p323) ∨ (¬ p657) ∨ (¬ p127)) : (¬ p347) ∨ p6 ∨ p224 ∨ p10 ∨ (¬ p1287) ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26076 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u6)

theorem step31167 (p6 p10 p127 p303 p323 p387 p1074 p1096 p1099 : Prop)
    (h26867 : p387 ∨ p303)
    (h26839 : p127 ∨ p6)
    (h26913 : p1099 ∨ p1096)
    (h26861 : p323 ∨ p10)
    (h26077 : (¬ p1074) ∨ (¬ p1099) ∨ (¬ p387) ∨ (¬ p323) ∨ (¬ p127)) : p303 ∨ p6 ∨ p1096 ∨ p10 ∨ (¬ p1074) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h26077 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u6)

theorem step31169 (p6 p10 p127 p161 p323 p434 p1229 p1232 p1330 : Prop)
    (h26861 : p323 ∨ p10)
    (h26839 : p127 ∨ p6)
    (h26927 : p1232 ∨ p1229)
    (h26079 : (¬ p161) ∨ (¬ p1232) ∨ (¬ p323) ∨ (¬ p127) ∨ (¬ p1330) ∨ (¬ p434)) : (¬ p434) ∨ (¬ p161) ∨ p10 ∨ p6 ∨ (¬ p1330) ∨ p1229 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26079 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u0)

theorem step31170 (p6 p101 p102 p127 p595 p616 p665 p1076 p1077 p1287 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26837 : p102 ∨ p101)
    (h26883 : p616 ∨ p595)
    (h26839 : p127 ∨ p6)
    (h26080 : (¬ p1287) ∨ (¬ p665) ∨ (¬ p616) ∨ (¬ p1077) ∨ (¬ p102) ∨ (¬ p127)) : p1076 ∨ p101 ∨ (¬ p665) ∨ p595 ∨ p6 ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1076) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p101) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h26080 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u9)

theorem step31171 (p6 p101 p102 p127 p344 p664 p1074 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26839 : p127 ∨ p6)
    (h26837 : p102 ∨ p101)
    (h26081 : (¬ p1074) ∨ (¬ p1099) ∨ (¬ p664) ∨ (¬ p127) ∨ (¬ p102) ∨ (¬ p344)) : (¬ p344) ∨ p1096 ∨ (¬ p1074) ∨ (¬ p664) ∨ p6 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u8 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26081 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u0)

theorem step31172 (p6 p101 p102 p127 p668 p897 p1076 p1077 p1096 p1099 : Prop)
    (h26839 : p127 ∨ p6)
    (h26911 : p1077 ∨ p1076)
    (h26913 : p1099 ∨ p1096)
    (h26837 : p102 ∨ p101)
    (h26082 : (¬ p897) ∨ (¬ p1077) ∨ (¬ p127) ∨ (¬ p1099) ∨ (¬ p668) ∨ (¬ p102)) : p6 ∨ p1076 ∨ (¬ p668) ∨ p1096 ∨ p101 ∨ (¬ p897) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p6) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p897 := by
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
    · exact False.elim (u1 q1)
  have u8 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h26082 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u9)

theorem step31173 (p6 p101 p102 p127 p290 p836 p840 p897 p1096 p1099 : Prop)
    (h26839 : p127 ∨ p6)
    (h26913 : p1099 ∨ p1096)
    (h26895 : p840 ∨ p836)
    (h26837 : p102 ∨ p101)
    (h26083 : (¬ p1099) ∨ (¬ p840) ∨ (¬ p290) ∨ (¬ p127) ∨ (¬ p897) ∨ (¬ p102)) : p6 ∨ (¬ p897) ∨ p1096 ∨ p836 ∨ (¬ p290) ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p6) := fun hu => hn (Or.inl hu)
  have u1 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p290 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26083 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u9)

theorem step31174 (p6 p101 p102 p127 p344 p595 p616 p1287 p1325 : Prop)
    (h26839 : p127 ∨ p6)
    (h26837 : p102 ∨ p101)
    (h26883 : p616 ∨ p595)
    (h26084 : (¬ p616) ∨ (¬ p1287) ∨ (¬ p344) ∨ (¬ p127) ∨ (¬ p1325) ∨ (¬ p102)) : (¬ p1325) ∨ (¬ p344) ∨ p6 ∨ p101 ∨ (¬ p1287) ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26084 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u7)

theorem step31177 (p2 p17 p83 p389 p419 p481 p576 p581 p996 p1249 p1493 : Prop)
    (h26873 : p481 ∨ p2)
    (h26879 : p581 ∨ p576)
    (h26905 : p996 ∨ p419)
    (h26087 : (¬ p1493) ∨ (¬ p1249) ∨ (¬ p581) ∨ (¬ p17) ∨ (¬ p481) ∨ (¬ p389) ∨ (¬ p996) ∨ (¬ p83)) : (¬ p1249) ∨ (¬ p1493) ∨ (¬ p389) ∨ p2 ∨ (¬ p17) ∨ p576 ∨ (¬ p83) ∨ p419 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1493 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h26087 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u6)

theorem step31178 (p6 p83 p101 p102 p127 p185 p642 p836 p897 p904 : Prop)
    (h26899 : p904 ∨ p897)
    (h26837 : p102 ∨ p101)
    (h26839 : p127 ∨ p6)
    (h26089 : (¬ p83) ∨ (¬ p642) ∨ (¬ p127) ∨ (¬ p102) ∨ (¬ p904) ∨ (¬ p185) ∨ (¬ p836)) : (¬ p836) ∨ p897 ∨ (¬ p642) ∨ p101 ∨ (¬ p83) ∨ (¬ p185) ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p897) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p642 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h26089 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u0)

theorem step31179 (p6 p83 p121 p127 p185 p918 p928 p1249 p1442 : Prop)
    (h26901 : p928 ∨ p918)
    (h26839 : p127 ∨ p6)
    (h26090 : (¬ p1249) ∨ (¬ p928) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p185) ∨ (¬ p1442) ∨ (¬ p83)) : p918 ∨ (¬ p1249) ∨ (¬ p185) ∨ (¬ p1442) ∨ (¬ p121) ∨ p6 ∨ (¬ p83) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p918) := fun hu => hn (Or.inl hu)
  have u1 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1442 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26090 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step31180 (p6 p41 p45 p83 p101 p102 p127 p344 p790 p814 p1385 p1393 : Prop)
    (h26831 : p45 ∨ p41)
    (h26839 : p127 ∨ p6)
    (h26893 : p814 ∨ p790)
    (h26837 : p102 ∨ p101)
    (h26933 : p1393 ∨ p1385)
    (h26091 : (¬ p1393) ∨ (¬ p83) ∨ (¬ p127) ∨ (¬ p344) ∨ (¬ p102) ∨ (¬ p45) ∨ (¬ p814)) : (¬ p344) ∨ p41 ∨ (¬ p83) ∨ p6 ∨ p790 ∨ p101 ∨ p1385 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p41) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u11 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h26091 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u11)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u9)

theorem step31181 (p6 p121 p127 p985 p1096 p1099 p1452 p1538 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26839 : p127 ∨ p6)
    (h26092 : (¬ p1538) ∨ (¬ p1099) ∨ (¬ p985) ∨ (¬ p121) ∨ (¬ p1452) ∨ (¬ p127)) : (¬ p1538) ∨ (¬ p985) ∨ (¬ p1452) ∨ (¬ p121) ∨ p1096 ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1538 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u7 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26092 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)

theorem step31182 (p6 p121 p127 p595 p616 p1335 p1452 p1545 : Prop)
    (h26883 : p616 ∨ p595)
    (h26839 : p127 ∨ p6)
    (h26093 : (¬ p1545) ∨ (¬ p616) ∨ (¬ p1335) ∨ (¬ p121) ∨ (¬ p1452) ∨ (¬ p127)) : (¬ p1452) ∨ (¬ p121) ∨ p595 ∨ (¬ p1335) ∨ p6 ∨ (¬ p1545) := by
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
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h26093 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u7)

theorem step31186 (p3 p12 p17 p41 p45 p83 p576 p581 p980 p983 : Prop)
    (h26903 : p983 ∨ p980)
    (h26831 : p45 ∨ p41)
    (h26879 : p581 ∨ p576)
    (h26097 : (¬ p581) ∨ (¬ p12) ∨ (¬ p983) ∨ (¬ p83) ∨ (¬ p17) ∨ (¬ p45) ∨ (¬ p3)) : (¬ p12) ∨ p980 ∨ (¬ p17) ∨ (¬ p3) ∨ (¬ p83) ∨ p41 ∨ p576 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u9 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h26097 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u3)

theorem step31187 (p3 p12 p63 p85 p665 p789 p858 p1385 : Prop)
    (h26897 : p858 ∨ p789)
    (h26835 : p85 ∨ p63)
    (h26099 : (¬ p858) ∨ (¬ p85) ∨ (¬ p12) ∨ (¬ p665) ∨ (¬ p3) ∨ (¬ p1385)) : p789 ∨ (¬ p12) ∨ (¬ p3) ∨ (¬ p665) ∨ (¬ p1385) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p789) := fun hu => hn (Or.inl hu)
  have u1 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26099 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u4)

theorem step31188 (p3 p12 p83 p790 p814 p1124 p1249 p1385 p1393 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h26893 : p814 ∨ p790)
    (h26100 : (¬ p1249) ∨ (¬ p1393) ∨ (¬ p12) ∨ (¬ p83) ∨ (¬ p814) ∨ (¬ p3) ∨ (¬ p1124)) : p1385 ∨ (¬ p12) ∨ p790 ∨ (¬ p83) ∨ (¬ p1249) ∨ (¬ p3) ∨ (¬ p1124) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1385) := fun hu => hn (Or.inl hu)
  have u1 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h26100 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)

theorem step31189 (p3 p224 p225 p431 p544 p595 p616 p657 p1545 : Prop)
    (h26877 : p544 ∨ p225)
    (h26883 : p616 ∨ p595)
    (h26887 : p657 ∨ p224)
    (h26101 : (¬ p1545) ∨ (¬ p616) ∨ (¬ p3) ∨ (¬ p431) ∨ (¬ p657) ∨ (¬ p544)) : (¬ p431) ∨ p225 ∨ p595 ∨ (¬ p3) ∨ (¬ p1545) ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26101 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u6)

theorem step31190 (p3 p163 p167 p327 p420 p424 p495 : Prop)
    (h26843 : p167 ∨ p163)
    (h26102 : (¬ p167) ∨ (¬ p420) ∨ (¬ p424) ∨ (¬ p495) ∨ (¬ p3) ∨ (¬ p327)) : (¬ p420) ∨ p163 ∨ (¬ p495) ∨ (¬ p424) ∨ (¬ p3) ∨ (¬ p327) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p327 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h26102 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)

theorem step31191 (p3 p163 p167 p424 p595 p616 p1287 p1325 : Prop)
    (h26843 : p167 ∨ p163)
    (h26883 : p616 ∨ p595)
    (h26103 : (¬ p1287) ∨ (¬ p616) ∨ (¬ p3) ∨ (¬ p167) ∨ (¬ p1325) ∨ (¬ p424)) : p163 ∨ p595 ∨ (¬ p1325) ∨ (¬ p1287) ∨ (¬ p424) ∨ (¬ p3) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p163) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p595) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h26103 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u4)

theorem step31192 (p6 p10 p63 p85 p127 p323 p347 p836 p918 : Prop)
    (h26839 : p127 ∨ p6)
    (h26835 : p85 ∨ p63)
    (h26861 : p323 ∨ p10)
    (h26104 : (¬ p918) ∨ (¬ p85) ∨ (¬ p323) ∨ (¬ p836) ∨ (¬ p127) ∨ (¬ p347)) : (¬ p836) ∨ (¬ p918) ∨ p6 ∨ p63 ∨ (¬ p347) ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26104 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u4)

theorem step31193 (p6 p63 p85 p121 p127 p258 p576 p1084 : Prop)
    (h26839 : p127 ∨ p6)
    (h26835 : p85 ∨ p63)
    (h26105 : (¬ p576) ∨ (¬ p85) ∨ (¬ p258) ∨ (¬ p127) ∨ (¬ p1084) ∨ (¬ p121)) : (¬ p258) ∨ p6 ∨ (¬ p121) ∨ p63 ∨ (¬ p1084) ∨ (¬ p576) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p576 := by
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
  rcases h26105 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u2)

theorem step31194 (p5 p15 p69 : Prop)
    (h26833 : p69 ∨ p15)
    (h16623 : p5 ∨ (¬ p69)) : p15 ∨ p5 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p15) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p5) := fun hu => hn (Or.inr hu)
  have u2 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h16623 with q0 | q1
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u2)

theorem step31196 (p15 p69 p234 p419 p1187 p1325 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26833 : p69 ∨ p15)
    (h17164 : (¬ p69) ∨ (¬ p419) ∨ (¬ p1187) ∨ (¬ p1325)) : p234 ∨ (¬ p419) ∨ (¬ p1325) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17164 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)

theorem step31197 (p15 p44 p69 p134 p330 p595 p1192 : Prop)
    (h26833 : p69 ∨ p15)
    (h19861 : (¬ p44) ∨ (¬ p69) ∨ (¬ p134) ∨ (¬ p330) ∨ (¬ p595) ∨ (¬ p1192)) : (¬ p44) ∨ p15 ∨ (¬ p134) ∨ (¬ p1192) ∨ (¬ p330) ∨ (¬ p595) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19861 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u3)

theorem step31198 (p15 p69 p124 p210 p304 p980 p1076 p1096 p1689 p1710 : Prop)
    (h26859 : p304 ∨ p124)
    (h26833 : p69 ∨ p15)
    (h16741 : (¬ p69) ∨ (¬ p210) ∨ (¬ p304) ∨ (¬ p980) ∨ (¬ p1076) ∨ (¬ p1096) ∨ (¬ p1689) ∨ (¬ p1710)) : (¬ p1710) ∨ (¬ p1689) ∨ (¬ p210) ∨ p124 ∨ p15 ∨ (¬ p1096) ∨ (¬ p1076) ∨ (¬ p980) := by
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
  have u2 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16741 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u0)

theorem step31200 (p15 p69 p595 p734 p1542 : Prop)
    (h26833 : p69 ∨ p15)
    (h17655 : (¬ p69) ∨ (¬ p595) ∨ (¬ p734) ∨ (¬ p1542)) : (¬ p1542) ∨ p15 ∨ (¬ p595) ∨ (¬ p734) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17655 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)

theorem step31201 (p15 p50 p69 p424 p595 p796 p1192 : Prop)
    (h26891 : p796 ∨ p424)
    (h26833 : p69 ∨ p15)
    (h16757 : (¬ p50) ∨ (¬ p69) ∨ (¬ p595) ∨ (¬ p796) ∨ (¬ p1192)) : p424 ∨ p15 ∨ (¬ p595) ∨ (¬ p50) ∨ (¬ p1192) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p50 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16757 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)

theorem step31202 (p15 p69 p419 p595 p1286 : Prop)
    (h26833 : p69 ∨ p15)
    (h17656 : (¬ p69) ∨ (¬ p419) ∨ (¬ p595) ∨ (¬ p1286)) : (¬ p1286) ∨ (¬ p595) ∨ p15 ∨ (¬ p419) := by
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
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17656 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)

theorem step31203 (p15 p39 p69 p88 p595 p789 p790 p814 p858 p1542 : Prop)
    (h26833 : p69 ∨ p15)
    (h26897 : p858 ∨ p789)
    (h26893 : p814 ∨ p790)
    (h26106 : (¬ p1542) ∨ (¬ p858) ∨ (¬ p595) ∨ (¬ p88) ∨ (¬ p69) ∨ (¬ p39) ∨ (¬ p814)) : (¬ p1542) ∨ p15 ∨ (¬ p88) ∨ (¬ p595) ∨ p789 ∨ (¬ p39) ∨ p790 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h26106 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u9)

theorem step31204 (p15 p69 p303 p419 p595 p996 p1192 : Prop)
    (h26905 : p996 ∨ p419)
    (h26833 : p69 ∨ p15)
    (h19620 : (¬ p69) ∨ (¬ p303) ∨ (¬ p595) ∨ (¬ p996) ∨ (¬ p1192)) : p419 ∨ (¬ p595) ∨ p15 ∨ (¬ p1192) ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19620 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)

theorem step31205 (p15 p69 p224 p595 p1286 : Prop)
    (h26833 : p69 ∨ p15)
    (h20482 : (¬ p69) ∨ (¬ p224) ∨ (¬ p595) ∨ (¬ p1286)) : (¬ p1286) ∨ (¬ p595) ∨ p15 ∨ (¬ p224) := by
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
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20482 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)

theorem step31207 (p15 p69 p224 p234 p419 p657 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26887 : p657 ∨ p224)
    (h26833 : p69 ∨ p15)
    (h18688 : (¬ p69) ∨ (¬ p419) ∨ (¬ p657) ∨ (¬ p1187)) : p234 ∨ p224 ∨ (¬ p419) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18688 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step31208 (p15 p69 p234 p303 p387 p419 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26867 : p387 ∨ p303)
    (h26833 : p69 ∨ p15)
    (h20027 : (¬ p69) ∨ (¬ p387) ∨ (¬ p419) ∨ (¬ p1187)) : p234 ∨ p303 ∨ (¬ p419) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20027 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step31209 (p15 p24 p69 p234 p326 p495 p499 p1187 : Prop)
    (h26875 : p499 ∨ p495)
    (h26921 : p1187 ∨ p234)
    (h26833 : p69 ∨ p15)
    (h16736 : (¬ p24) ∨ (¬ p69) ∨ (¬ p326) ∨ (¬ p499) ∨ (¬ p1187)) : p495 ∨ p234 ∨ p15 ∨ (¬ p24) ∨ (¬ p326) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p495) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p234) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p326 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16736 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)

theorem step31210 (p14 p15 p69 p229 p538 p595 p1192 : Prop)
    (h26849 : p229 ∨ p14)
    (h26833 : p69 ∨ p15)
    (h16809 : (¬ p69) ∨ (¬ p229) ∨ (¬ p538) ∨ (¬ p595) ∨ (¬ p1192)) : (¬ p538) ∨ p14 ∨ (¬ p1192) ∨ p15 ∨ (¬ p595) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p538 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p14) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16809 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u2)

theorem step31212 (p15 p39 p69 p88 p238 p419 p431 p595 p667 p734 p996 p1055 p1192 : Prop)
    (h26905 : p996 ∨ p419)
    (h26833 : p69 ∨ p15)
    (h19071 : (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p238) ∨ (¬ p431) ∨ (¬ p595) ∨ (¬ p667) ∨ (¬ p734) ∨ (¬ p996) ∨ (¬ p1055) ∨ (¬ p1192)) : (¬ p734) ∨ p419 ∨ (¬ p238) ∨ (¬ p88) ∨ (¬ p595) ∨ p15 ∨ (¬ p39) ∨ (¬ p1192) ∨ (¬ p431) ∨ (¬ p667) ∨ (¬ p1055) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p419) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p667 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u12 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19071 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u12)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u0)
  · exact False.elim (q8 u11)
  · exact False.elim (q9 u10)
  · exact False.elim (q10 u7)

theorem step31213 (p15 p39 p69 p88 p238 p595 p836 p1055 p1115 p1116 p1286 : Prop)
    (h26833 : p69 ∨ p15)
    (h26915 : p1116 ∨ p1115)
    (h20451 : (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p238) ∨ (¬ p595) ∨ (¬ p836) ∨ (¬ p1055) ∨ (¬ p1116) ∨ (¬ p1286)) : (¬ p836) ∨ p15 ∨ (¬ p238) ∨ (¬ p1055) ∨ (¬ p595) ∨ (¬ p1286) ∨ p1115 ∨ (¬ p39) ∨ (¬ p88) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1055 := by
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
  have u6 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20451 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u5)

theorem step31215 (p15 p69 p124 p234 p419 p496 p665 p1076 p1077 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26911 : p1077 ∨ p1076)
    (h26833 : p69 ∨ p15)
    (h17485 : (¬ p69) ∨ (¬ p124) ∨ (¬ p419) ∨ (¬ p496) ∨ (¬ p665) ∨ (¬ p1077) ∨ (¬ p1187)) : p234 ∨ p1076 ∨ (¬ p124) ∨ (¬ p496) ∨ (¬ p665) ∨ p15 ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
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
  have u5 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17485 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u7)

theorem step31216 (p14 p15 p69 p134 p163 p229 : Prop)
    (h26849 : p229 ∨ p14)
    (h26833 : p69 ∨ p15)
    (h17525 : (¬ p69) ∨ (¬ p134) ∨ (¬ p163) ∨ (¬ p229)) : p14 ∨ (¬ p163) ∨ (¬ p134) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17525 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)

theorem step31217 (p12 p15 p44 p63 p69 p163 p167 p1036 : Prop)
    (h26907 : p1036 ∨ p12)
    (h26843 : p167 ∨ p163)
    (h26833 : p69 ∨ p15)
    (h19961 : (¬ p44) ∨ (¬ p63) ∨ (¬ p69) ∨ (¬ p167) ∨ (¬ p1036)) : (¬ p44) ∨ p12 ∨ (¬ p63) ∨ p163 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19961 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step31219 (p15 p39 p69 p88 p161 p790 p814 p1015 p1225 p1229 p1335 : Prop)
    (h26925 : p1225 ∨ p161)
    (h26893 : p814 ∨ p790)
    (h26833 : p69 ∨ p15)
    (h19047 : (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p814) ∨ (¬ p1015) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1335)) : p161 ∨ (¬ p1015) ∨ (¬ p88) ∨ (¬ p1335) ∨ (¬ p39) ∨ (¬ p1229) ∨ p790 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p161) := fun hu => hn (Or.inl hu)
  have u1 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h19047 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u3)

theorem step31220 (p11 p15 p39 p69 p88 p258 p261 p419 p595 p961 p996 p1192 p1443 : Prop)
    (h26935 : p1443 ∨ p11)
    (h26833 : p69 ∨ p15)
    (h26905 : p996 ∨ p419)
    (h20446 : (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p258) ∨ (¬ p261) ∨ (¬ p595) ∨ (¬ p961) ∨ (¬ p996) ∨ (¬ p1192) ∨ (¬ p1443)) : (¬ p961) ∨ p11 ∨ (¬ p595) ∨ (¬ p258) ∨ (¬ p39) ∨ p15 ∨ (¬ p261) ∨ (¬ p88) ∨ p419 ∨ (¬ p1192) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p11) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u11 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u12 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h20446 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u11)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u12)
  · exact False.elim (q8 u9)
  · exact False.elim (q9 u10)

theorem step31222 (p15 p69 p125 p303 p362 p387 p496 p1325 p1333 p1473 p1710 : Prop)
    (h26867 : p387 ∨ p303)
    (h26833 : p69 ∨ p15)
    (h26931 : p1333 ∨ p1325)
    (h26865 : p362 ∨ p125)
    (h17595 : (¬ p69) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p496) ∨ (¬ p1333) ∨ (¬ p1473) ∨ (¬ p1710)) : (¬ p1710) ∨ p303 ∨ p15 ∨ p1325 ∨ (¬ p1473) ∨ (¬ p496) ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1473 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h17595 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u0)

theorem step31223 (p15 p18 p69 p121 p160 p389 p1206 p1233 p1325 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26833 : p69 ∨ p15)
    (h19841 : (¬ p18) ∨ (¬ p69) ∨ (¬ p160) ∨ (¬ p389) ∨ (¬ p1206) ∨ (¬ p1233) ∨ (¬ p1325)) : (¬ p160) ∨ p121 ∨ (¬ p1233) ∨ (¬ p1325) ∨ (¬ p18) ∨ p15 ∨ (¬ p389) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p121) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1233 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19841 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step31224 (p14 p15 p69 p229 p382 p406 p816 p940 p985 p1325 p1333 p1385 p1393 : Prop)
    (h26849 : p229 ∨ p14)
    (h26933 : p1393 ∨ p1385)
    (h26833 : p69 ∨ p15)
    (h26869 : p406 ∨ p382)
    (h26931 : p1333 ∨ p1325)
    (h20555 : (¬ p69) ∨ (¬ p229) ∨ (¬ p406) ∨ (¬ p816) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1333) ∨ (¬ p1393)) : (¬ p940) ∨ p14 ∨ p1385 ∨ (¬ p816) ∨ p15 ∨ p382 ∨ p1325 ∨ (¬ p985) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p14) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p816 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u12 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20555 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u12)
  · exact False.elim (q7 u9)

theorem step31226 (p15 p39 p69 p88 p185 p419 p595 p996 p1115 p1192 : Prop)
    (h26833 : p69 ∨ p15)
    (h26905 : p996 ∨ p419)
    (h26109 : (¬ p1115) ∨ (¬ p595) ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p1192) ∨ (¬ p88) ∨ (¬ p996) ∨ (¬ p185)) : (¬ p595) ∨ (¬ p1115) ∨ (¬ p88) ∨ p15 ∨ (¬ p39) ∨ p419 ∨ (¬ p1192) ∨ (¬ p185) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26109 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u7)

theorem step31227 (p15 p18 p69 p101 p258 p288 : Prop)
    (h26855 : p288 ∨ p258)
    (h26833 : p69 ∨ p15)
    (h16608 : (¬ p18) ∨ (¬ p69) ∨ (¬ p101) ∨ (¬ p288)) : (¬ p101) ∨ p258 ∨ (¬ p18) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p258) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16608 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)

theorem step31228 (p15 p18 p69 p101 p344 p346 : Prop)
    (h26863 : p346 ∨ p344)
    (h26833 : p69 ∨ p15)
    (h17365 : (¬ p18) ∨ (¬ p69) ∨ (¬ p101) ∨ (¬ p346)) : (¬ p101) ∨ p344 ∨ (¬ p18) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17365 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)

theorem step31229 (p15 p20 p69 p101 p121 p455 p456 : Prop)
    (h26871 : p456 ∨ p455)
    (h26833 : p69 ∨ p15)
    (h19723 : (¬ p20) ∨ (¬ p69) ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p456)) : (¬ p101) ∨ p455 ∨ (¬ p20) ∨ p15 ∨ (¬ p121) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p455) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p20 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19723 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)

theorem step31230 (p10 p15 p18 p69 p303 : Prop)
    (h26833 : p69 ∨ p15)
    (h21024 : (¬ p10) ∨ (¬ p18) ∨ (¬ p69) ∨ (¬ p303)) : (¬ p10) ∨ (¬ p303) ∨ p15 ∨ (¬ p18) := by
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
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h21024 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)

theorem step31231 (p10 p15 p18 p69 p86 p185 p237 p351 p836 p840 : Prop)
    (h26833 : p69 ∨ p15)
    (h26851 : p237 ∨ p185)
    (h26895 : p840 ∨ p836)
    (h18717 : (¬ p10) ∨ (¬ p18) ∨ (¬ p69) ∨ (¬ p86) ∨ (¬ p237) ∨ (¬ p351) ∨ (¬ p840)) : (¬ p10) ∨ p15 ∨ p185 ∨ p836 ∨ (¬ p86) ∨ (¬ p351) ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18717 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u9)

theorem step31232 (p10 p15 p18 p69 p185 p517 p790 p918 p928 : Prop)
    (h26901 : p928 ∨ p918)
    (h26833 : p69 ∨ p15)
    (h18718 : (¬ p10) ∨ (¬ p18) ∨ (¬ p69) ∨ (¬ p185) ∨ (¬ p517) ∨ (¬ p790) ∨ (¬ p928)) : (¬ p517) ∨ (¬ p185) ∨ (¬ p790) ∨ p918 ∨ (¬ p10) ∨ p15 ∨ (¬ p18) := by
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
  have u2 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18718 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u7)

theorem step31233 (p10 p15 p18 p69 p438 : Prop)
    (h26833 : p69 ∨ p15)
    (h19704 : (¬ p10) ∨ (¬ p18) ∨ (¬ p69) ∨ (¬ p438)) : (¬ p10) ∨ (¬ p438) ∨ p15 ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19704 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)

theorem step31234 (p10 p15 p18 p69 p224 p351 p382 p406 p617 : Prop)
    (h26869 : p406 ∨ p382)
    (h26833 : p69 ∨ p15)
    (h19726 : (¬ p10) ∨ (¬ p18) ∨ (¬ p69) ∨ (¬ p224) ∨ (¬ p351) ∨ (¬ p406) ∨ (¬ p617)) : p382 ∨ (¬ p10) ∨ p15 ∨ (¬ p18) ∨ (¬ p351) ∨ (¬ p224) ∨ (¬ p617) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p18 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p617 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19726 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u6)

theorem step31235 (p10 p15 p18 p69 p382 p406 p517 p617 p789 p858 : Prop)
    (h26897 : p858 ∨ p789)
    (h26833 : p69 ∨ p15)
    (h26869 : p406 ∨ p382)
    (h20318 : (¬ p10) ∨ (¬ p18) ∨ (¬ p69) ∨ (¬ p406) ∨ (¬ p517) ∨ (¬ p617) ∨ (¬ p858)) : (¬ p517) ∨ (¬ p10) ∨ p789 ∨ (¬ p617) ∨ p15 ∨ (¬ p18) ∨ p382 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p517 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p617 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20318 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step31236 (p14 p15 p69 p225 p229 p734 : Prop)
    (h26849 : p229 ∨ p14)
    (h26833 : p69 ∨ p15)
    (h17944 : (¬ p69) ∨ (¬ p225) ∨ (¬ p229) ∨ (¬ p734)) : p14 ∨ (¬ p225) ∨ p15 ∨ (¬ p734) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p734 := by
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
    · exact False.elim (u2 q1)
  rcases h17944 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)

theorem step31237 (p14 p15 p69 p225 p229 p344 : Prop)
    (h26849 : p229 ∨ p14)
    (h26833 : p69 ∨ p15)
    (h19516 : (¬ p69) ∨ (¬ p225) ∨ (¬ p229) ∨ (¬ p344)) : p14 ∨ (¬ p344) ∨ (¬ p225) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19516 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)

theorem step31238 (p14 p15 p69 p225 p229 p303 p347 p382 p406 p617 : Prop)
    (h26869 : p406 ∨ p382)
    (h26849 : p229 ∨ p14)
    (h26833 : p69 ∨ p15)
    (h19875 : (¬ p69) ∨ (¬ p225) ∨ (¬ p229) ∨ (¬ p303) ∨ (¬ p347) ∨ (¬ p406) ∨ (¬ p617)) : p382 ∨ p14 ∨ (¬ p225) ∨ (¬ p617) ∨ (¬ p347) ∨ p15 ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p14) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p617 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19875 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step31239 (p14 p15 p69 p224 p225 p229 : Prop)
    (h26849 : p229 ∨ p14)
    (h26833 : p69 ∨ p15)
    (h16287 : (¬ p69) ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p229)) : p14 ∨ (¬ p225) ∨ (¬ p224) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16287 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)

theorem step31241 (p14 p15 p17 p69 p86 p126 p225 p229 p256 p347 : Prop)
    (h26849 : p229 ∨ p14)
    (h26853 : p256 ∨ p17)
    (h26833 : p69 ∨ p15)
    (h18863 : (¬ p69) ∨ (¬ p86) ∨ (¬ p126) ∨ (¬ p225) ∨ (¬ p229) ∨ (¬ p256) ∨ (¬ p347)) : p14 ∨ p17 ∨ (¬ p126) ∨ (¬ p225) ∨ (¬ p86) ∨ (¬ p347) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18863 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u5)

theorem step31242 (p15 p18 p69 p121 p349 p382 p389 p406 p434 p690 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26833 : p69 ∨ p15)
    (h26869 : p406 ∨ p382)
    (h19703 : (¬ p18) ∨ (¬ p69) ∨ (¬ p349) ∨ (¬ p389) ∨ (¬ p406) ∨ (¬ p434) ∨ (¬ p690) ∨ (¬ p1206)) : (¬ p690) ∨ (¬ p434) ∨ p121 ∨ (¬ p389) ∨ p15 ∨ p382 ∨ (¬ p18) ∨ (¬ p349) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p121) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19703 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u8)

theorem step31243 (p15 p39 p69 p382 p406 p620 p1287 p1387 : Prop)
    (h26869 : p406 ∨ p382)
    (h26833 : p69 ∨ p15)
    (h17801 : (¬ p39) ∨ (¬ p69) ∨ (¬ p406) ∨ (¬ p620) ∨ (¬ p1287) ∨ (¬ p1387)) : p382 ∨ (¬ p620) ∨ (¬ p1387) ∨ (¬ p1287) ∨ p15 ∨ (¬ p39) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p620 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17801 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u2)

theorem step31244 (p15 p63 p69 p124 p210 p304 p344 p346 p423 p734 p1141 p1209 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26833 : p69 ∨ p15)
    (h26863 : p346 ∨ p344)
    (h26859 : p304 ∨ p124)
    (h20105 : (¬ p63) ∨ (¬ p69) ∨ (¬ p210) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p734) ∨ (¬ p1141) ∨ (¬ p1209)) : p423 ∨ (¬ p210) ∨ p15 ∨ p344 ∨ (¬ p63) ∨ (¬ p734) ∨ (¬ p1209) ∨ p124 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h20105 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u6)

theorem step31245 (p15 p39 p69 p89 p185 p237 p918 : Prop)
    (h26851 : p237 ∨ p185)
    (h26833 : p69 ∨ p15)
    (h16312 : (¬ p39) ∨ (¬ p69) ∨ (¬ p89) ∨ (¬ p237) ∨ (¬ p918)) : p185 ∨ (¬ p918) ∨ p15 ∨ (¬ p39) ∨ (¬ p89) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p185) := fun hu => hn (Or.inl hu)
  have u1 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16312 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)

theorem step31246 (p15 p18 p69 p121 p532 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26833 : p69 ∨ p15)
    (h18956 : (¬ p18) ∨ (¬ p69) ∨ (¬ p532) ∨ (¬ p1206)) : p121 ∨ (¬ p18) ∨ (¬ p532) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18956 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step31247 (p14 p15 p69 p86 p185 p225 p229 p237 p668 p1115 p1116 : Prop)
    (h26849 : p229 ∨ p14)
    (h26915 : p1116 ∨ p1115)
    (h26851 : p237 ∨ p185)
    (h26833 : p69 ∨ p15)
    (h19720 : (¬ p69) ∨ (¬ p86) ∨ (¬ p225) ∨ (¬ p229) ∨ (¬ p237) ∨ (¬ p668) ∨ (¬ p1116)) : p14 ∨ p1115 ∨ p185 ∨ (¬ p86) ∨ p15 ∨ (¬ p225) ∨ (¬ p668) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1115) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19720 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u8)

theorem step31248 (p12 p15 p39 p69 p88 p665 p789 p790 p814 p858 p883 p1096 : Prop)
    (h26833 : p69 ∨ p15)
    (h26897 : p858 ∨ p789)
    (h26893 : p814 ∨ p790)
    (h19170 : (¬ p12) ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p665) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p883) ∨ (¬ p1096)) : (¬ p12) ∨ p15 ∨ p789 ∨ p790 ∨ (¬ p883) ∨ (¬ p1096) ∨ (¬ p665) ∨ (¬ p39) ∨ (¬ p88) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p883 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19170 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)

theorem step31252 (p15 p69 p423 p980 p983 p1141 p1465 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26903 : p983 ∨ p980)
    (h26833 : p69 ∨ p15)
    (h19683 : (¬ p69) ∨ (¬ p983) ∨ (¬ p1141) ∨ (¬ p1465)) : p423 ∨ p980 ∨ p15 ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19683 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)

theorem step31253 (p15 p69 p234 p435 p980 p983 p1055 p1061 p1187 p1335 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26903 : p983 ∨ p980)
    (h26909 : p1061 ∨ p1055)
    (h26833 : p69 ∨ p15)
    (h22761 : (¬ p435) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p69) ∨ (¬ p1187) ∨ (¬ p1335)) : p234 ∨ p980 ∨ (¬ p435) ∨ p1055 ∨ (¬ p1335) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h22761 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u4)

theorem step31254 (p15 p63 p69 p422 p423 p1141 p1256 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26833 : p69 ∨ p15)
    (h26929 : p1256 ∨ p422)
    (h20057 : (¬ p63) ∨ (¬ p69) ∨ (¬ p1141) ∨ (¬ p1256)) : p423 ∨ p15 ∨ (¬ p63) ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20057 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)

theorem step31256 (p15 p44 p63 p69 p422 p1465 : Prop)
    (h26833 : p69 ∨ p15)
    (h19814 : (¬ p44) ∨ (¬ p63) ∨ (¬ p69) ∨ (¬ p422) ∨ (¬ p1465)) : (¬ p1465) ∨ (¬ p422) ∨ (¬ p44) ∨ (¬ p63) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19814 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)

theorem step31257 (p14 p15 p69 p229 p980 p983 p1037 p1465 : Prop)
    (h26903 : p983 ∨ p980)
    (h26849 : p229 ∨ p14)
    (h26833 : p69 ∨ p15)
    (h19763 : (¬ p69) ∨ (¬ p229) ∨ (¬ p983) ∨ (¬ p1037) ∨ (¬ p1465)) : (¬ p1037) ∨ (¬ p1465) ∨ p980 ∨ p14 ∨ p15 := by
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
  have u2 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19763 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)

theorem step31258 (p15 p69 p125 p362 p423 p434 p496 p1141 p1330 p1465 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26865 : p362 ∨ p125)
    (h26833 : p69 ∨ p15)
    (h17152 : (¬ p69) ∨ (¬ p362) ∨ (¬ p434) ∨ (¬ p496) ∨ (¬ p1141) ∨ (¬ p1330) ∨ (¬ p1465)) : (¬ p434) ∨ p423 ∨ p125 ∨ (¬ p1465) ∨ (¬ p1330) ∨ p15 ∨ (¬ p496) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p423) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17152 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u3)

theorem step31259 (p15 p69 p86 p423 p790 p1022 p1141 p1330 p1465 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26833 : p69 ∨ p15)
    (h17174 : (¬ p69) ∨ (¬ p86) ∨ (¬ p790) ∨ (¬ p1022) ∨ (¬ p1141) ∨ (¬ p1330) ∨ (¬ p1465)) : (¬ p1022) ∨ p423 ∨ (¬ p86) ∨ p15 ∨ (¬ p790) ∨ (¬ p1330) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p423) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p790 := by
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
  have u7 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17174 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)

theorem step31260 (p12 p14 p15 p69 p229 p980 p1036 : Prop)
    (h26849 : p229 ∨ p14)
    (h26907 : p1036 ∨ p12)
    (h26833 : p69 ∨ p15)
    (h18967 : (¬ p69) ∨ (¬ p229) ∨ (¬ p980) ∨ (¬ p1036)) : p14 ∨ p12 ∨ p15 ∨ (¬ p980) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18967 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)

theorem step31261 (p15 p69 p422 p423 p424 p796 p1141 p1256 : Prop)
    (h26891 : p796 ∨ p424)
    (h26917 : p1141 ∨ p423)
    (h26929 : p1256 ∨ p422)
    (h26833 : p69 ∨ p15)
    (h18504 : (¬ p69) ∨ (¬ p796) ∨ (¬ p1141) ∨ (¬ p1256)) : p424 ∨ p423 ∨ p422 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p423) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18504 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)

theorem step31262 (p15 p69 p134 p422 p423 p1141 p1256 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26929 : p1256 ∨ p422)
    (h26833 : p69 ∨ p15)
    (h16857 : (¬ p69) ∨ (¬ p134) ∨ (¬ p1141) ∨ (¬ p1256)) : p423 ∨ p422 ∨ p15 ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p422) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16857 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step31263 (p15 p50 p69 p422 p1145 p1229 : Prop)
    (h26833 : p69 ∨ p15)
    (h16735 : (¬ p50) ∨ (¬ p69) ∨ (¬ p422) ∨ (¬ p1145) ∨ (¬ p1229)) : (¬ p1145) ∨ (¬ p422) ∨ (¬ p50) ∨ (¬ p1229) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1145 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p50 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16735 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u3)

theorem step31264 (p15 p69 p86 p124 p126 p234 p258 p266 p331 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26833 : p69 ∨ p15)
    (h19759 : (¬ p69) ∨ (¬ p86) ∨ (¬ p124) ∨ (¬ p126) ∨ (¬ p258) ∨ (¬ p266) ∨ (¬ p331) ∨ (¬ p1187)) : p234 ∨ (¬ p266) ∨ (¬ p258) ∨ (¬ p331) ∨ (¬ p126) ∨ (¬ p124) ∨ p15 ∨ (¬ p86) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p331 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p86 := by
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
    · exact False.elim (u6 q1)
  rcases h19759 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u8)

theorem step31265 (p15 p17 p39 p69 p88 p161 p258 p1076 p1225 p1229 : Prop)
    (h26833 : p69 ∨ p15)
    (h26925 : p1225 ∨ p161)
    (h20064 : (¬ p17) ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p258) ∨ (¬ p1076) ∨ (¬ p1225) ∨ (¬ p1229)) : (¬ p258) ∨ (¬ p1229) ∨ p15 ∨ (¬ p17) ∨ (¬ p39) ∨ (¬ p88) ∨ p161 ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p161) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20064 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u1)

theorem step31266 (p15 p17 p39 p69 p88 p161 p258 p344 p346 p1225 p1229 : Prop)
    (h26925 : p1225 ∨ p161)
    (h26833 : p69 ∨ p15)
    (h26863 : p346 ∨ p344)
    (h20448 : (¬ p17) ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p258) ∨ (¬ p346) ∨ (¬ p1225) ∨ (¬ p1229)) : p161 ∨ (¬ p258) ∨ (¬ p39) ∨ (¬ p88) ∨ (¬ p1229) ∨ p15 ∨ p344 ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p161) := fun hu => hn (Or.inl hu)
  have u1 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20448 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u4)

theorem step31268 (p15 p20 p69 p495 p499 : Prop)
    (h26875 : p499 ∨ p495)
    (h26833 : p69 ∨ p15)
    (h11153 : (¬ p20) ∨ (¬ p69) ∨ (¬ p499)) : p495 ∨ p15 ∨ (¬ p20) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p495) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p20 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h11153 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)

theorem step31269 (p15 p69 p125 p234 p303 p362 p387 p431 p435 p496 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26867 : p387 ∨ p303)
    (h26865 : p362 ∨ p125)
    (h26833 : p69 ∨ p15)
    (h17156 : (¬ p69) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p431) ∨ (¬ p435) ∨ (¬ p496) ∨ (¬ p1187)) : p234 ∨ (¬ p431) ∨ p303 ∨ p125 ∨ (¬ p496) ∨ (¬ p435) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h17156 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u7)

theorem step31270 (p15 p69 p227 p234 p435 p496 p1187 p1335 p1452 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26833 : p69 ∨ p15)
    (h17159 : (¬ p69) ∨ (¬ p227) ∨ (¬ p435) ∨ (¬ p496) ∨ (¬ p1187) ∨ (¬ p1335) ∨ (¬ p1452)) : (¬ p1452) ∨ p234 ∨ (¬ p435) ∨ (¬ p1335) ∨ (¬ p227) ∨ p15 ∨ (¬ p496) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p234) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p496 := by
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
  rcases h17159 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u0)

theorem step31271 (p15 p26 p69 p125 p362 p420 p498 : Prop)
    (h26865 : p362 ∨ p125)
    (h26833 : p69 ∨ p15)
    (h17283 : (¬ p26) ∨ (¬ p69) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p498)) : (¬ p26) ∨ (¬ p420) ∨ p125 ∨ (¬ p498) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p26 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17283 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)

theorem step31272 (p17 p18 p140 p189 p256 : Prop)
    (h26853 : p256 ∨ p17)
    (h26110 : (¬ p256) ∨ (¬ p18) ∨ (¬ p189) ∨ (¬ p140)) : p17 ∨ (¬ p18) ∨ (¬ p189) ∨ (¬ p140) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p17) := fun hu => hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
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
  rcases h26110 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)

theorem step31273 (p189 p234 p790 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26111 : (¬ p790) ∨ (¬ p1187) ∨ (¬ p189)) : p234 ∨ (¬ p790) ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h26111 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)

theorem step31274 (p18 p121 p141 p227 p262 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26113 : (¬ p1206) ∨ (¬ p227) ∨ (¬ p18) ∨ (¬ p262) ∨ (¬ p141)) : p121 ∨ (¬ p227) ∨ (¬ p18) ∨ (¬ p141) ∨ (¬ p262) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h26113 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)

theorem step31282 (p6 p18 p43 p127 p161 p980 p1044 p1140 p1159 p1225 p1229 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26925 : p1225 ∨ p161)
    (h26839 : p127 ∨ p6)
    (h20590 : (¬ p18) ∨ (¬ p43) ∨ (¬ p127) ∨ (¬ p980) ∨ (¬ p1044) ∨ (¬ p1159) ∨ (¬ p1225) ∨ (¬ p1229)) : p1140 ∨ p161 ∨ (¬ p43) ∨ (¬ p1229) ∨ p6 ∨ (¬ p980) ∨ (¬ p18) ∨ (¬ p1044) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p161) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1044 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20590 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u3)

theorem step31285 (p3 p14 p43 p187 p229 p422 p1465 : Prop)
    (h26849 : p229 ∨ p14)
    (h19378 : (¬ p3) ∨ (¬ p43) ∨ (¬ p187) ∨ (¬ p229) ∨ (¬ p422) ∨ (¬ p1465)) : p14 ∨ (¬ p3) ∨ (¬ p1465) ∨ (¬ p187) ∨ (¬ p422) ∨ (¬ p43) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19378 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u2)

theorem step31286 (p43 p135 p234 p424 p576 p581 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26879 : p581 ∨ p576)
    (h20420 : (¬ p43) ∨ (¬ p135) ∨ (¬ p424) ∨ (¬ p581) ∨ (¬ p1187)) : p234 ∨ (¬ p43) ∨ (¬ p135) ∨ (¬ p424) ∨ p576 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20420 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step31287 (p3 p14 p43 p71 p229 p495 p577 : Prop)
    (h26849 : p229 ∨ p14)
    (h18112 : (¬ p3) ∨ (¬ p43) ∨ (¬ p71) ∨ (¬ p229) ∨ (¬ p495) ∨ (¬ p577)) : p14 ∨ (¬ p3) ∨ (¬ p495) ∨ (¬ p71) ∨ (¬ p43) ∨ (¬ p577) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h18112 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u5)

theorem step31288 (p43 p71 p423 p495 p577 p1140 p1141 : Prop)
    (h26917 : p1141 ∨ p423)
    (h19466 : (¬ p43) ∨ (¬ p71) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p1140) ∨ (¬ p1141)) : (¬ p1140) ∨ p423 ∨ (¬ p577) ∨ (¬ p495) ∨ (¬ p71) ∨ (¬ p43) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p423) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19466 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u6)

theorem step31290 (p43 p63 p85 p134 p234 p424 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26835 : p85 ∨ p63)
    (h18908 : (¬ p43) ∨ (¬ p85) ∨ (¬ p134) ∨ (¬ p424) ∨ (¬ p1187)) : p234 ∨ (¬ p424) ∨ p63 ∨ (¬ p134) ∨ (¬ p43) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18908 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)

theorem step31291 (p43 p135 p283 p422 p423 p834 p1141 p1256 p1385 p1393 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26933 : p1393 ∨ p1385)
    (h26929 : p1256 ∨ p422)
    (h20053 : (¬ p43) ∨ (¬ p135) ∨ (¬ p283) ∨ (¬ p834) ∨ (¬ p1141) ∨ (¬ p1256) ∨ (¬ p1393)) : p423 ∨ p1385 ∨ p422 ∨ (¬ p283) ∨ (¬ p834) ∨ (¬ p43) ∨ (¬ p135) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1385) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p283 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p834 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20053 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u8)

theorem step31294 (p3 p12 p39 p63 p68 p642 p1076 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h17619 : (¬ p3) ∨ (¬ p12) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p642) ∨ (¬ p1076) ∨ (¬ p1099)) : p1096 ∨ (¬ p12) ∨ (¬ p3) ∨ (¬ p1076) ∨ (¬ p63) ∨ (¬ p39) ∨ (¬ p68) ∨ (¬ p642) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1096) := fun hu => hn (Or.inl hu)
  have u1 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
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
  have u6 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p642 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17619 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u8)

theorem step31295 (p3 p12 p39 p68 p126 p301 p303 p576 p665 : Prop)
    (h26857 : p301 ∨ p126)
    (h19167 : (¬ p3) ∨ (¬ p12) ∨ (¬ p39) ∨ (¬ p68) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p576) ∨ (¬ p665)) : p126 ∨ (¬ p3) ∨ (¬ p39) ∨ (¬ p665) ∨ (¬ p12) ∨ (¬ p303) ∨ (¬ p68) ∨ (¬ p576) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19167 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u3)

theorem step31296 (p3 p12 p39 p63 p68 p595 p616 p665 p789 p858 p1388 : Prop)
    (h26883 : p616 ∨ p595)
    (h26897 : p858 ∨ p789)
    (h19264 : (¬ p3) ∨ (¬ p12) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p616) ∨ (¬ p665) ∨ (¬ p858) ∨ (¬ p1388)) : p595 ∨ (¬ p1388) ∨ p789 ∨ (¬ p12) ∨ (¬ p39) ∨ (¬ p68) ∨ (¬ p665) ∨ (¬ p3) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p595) := fun hu => hn (Or.inl hu)
  have u1 : p1388 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p63 := by
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
    · exact False.elim (u2 q1)
  rcases h19264 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u1)

theorem step31297 (p3 p12 p39 p68 p88 p790 p814 p980 p983 p1015 p1335 : Prop)
    (h26903 : p983 ∨ p980)
    (h26893 : p814 ∨ p790)
    (h19613 : (¬ p3) ∨ (¬ p12) ∨ (¬ p39) ∨ (¬ p68) ∨ (¬ p88) ∨ (¬ p814) ∨ (¬ p983) ∨ (¬ p1015) ∨ (¬ p1335)) : (¬ p12) ∨ p980 ∨ (¬ p39) ∨ p790 ∨ (¬ p88) ∨ (¬ p3) ∨ (¬ p1335) ∨ (¬ p1015) ∨ (¬ p68) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19613 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u6)

theorem step31299 (p15 p17 p39 p69 p89 p256 p576 : Prop)
    (h26853 : p256 ∨ p17)
    (h26833 : p69 ∨ p15)
    (h17201 : (¬ p39) ∨ (¬ p69) ∨ (¬ p89) ∨ (¬ p256) ∨ (¬ p576)) : p17 ∨ p15 ∨ (¬ p89) ∨ (¬ p576) ∨ (¬ p39) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p17) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17201 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)

theorem step31309 (p23 p455 p456 p532 p1035 p1212 : Prop)
    (h26871 : p456 ∨ p455)
    (h19951 : (¬ p23) ∨ (¬ p456) ∨ (¬ p532) ∨ (¬ p1035) ∨ (¬ p1212)) : p455 ∨ (¬ p1035) ∨ (¬ p23) ∨ (¬ p1212) ∨ (¬ p532) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p23 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1212 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19951 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)

theorem step31310 (p8 p23 p108 p225 p309 p544 p633 p636 p710 : Prop)
    (h26885 : p636 ∨ p633)
    (h26889 : p710 ∨ p8)
    (h26877 : p544 ∨ p225)
    (h19439 : (¬ p23) ∨ (¬ p108) ∨ (¬ p309) ∨ (¬ p544) ∨ (¬ p636) ∨ (¬ p710)) : p633 ∨ (¬ p309) ∨ (¬ p23) ∨ p8 ∨ (¬ p108) ∨ p225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p23 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19439 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)

theorem step31311 (p12 p23 p108 p309 p633 p636 p1055 : Prop)
    (h26885 : p636 ∨ p633)
    (h19440 : (¬ p12) ∨ (¬ p23) ∨ (¬ p108) ∨ (¬ p309) ∨ (¬ p636) ∨ (¬ p1055)) : p633 ∨ (¬ p309) ∨ (¬ p23) ∨ (¬ p1055) ∨ (¬ p108) ∨ (¬ p12) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p23 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19440 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)

theorem step31312 (p23 p121 p458 p495 p499 p1229 p1232 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h26875 : p499 ∨ p495)
    (h16368 : (¬ p23) ∨ (¬ p121) ∨ (¬ p458) ∨ (¬ p499) ∨ (¬ p1232)) : (¬ p458) ∨ p1229 ∨ (¬ p121) ∨ (¬ p23) ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p458 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p23 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16368 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step31313 (p23 p134 p422 p455 p456 p1211 p1256 : Prop)
    (h26871 : p456 ∨ p455)
    (h26929 : p1256 ∨ p422)
    (h19388 : (¬ p23) ∨ (¬ p134) ∨ (¬ p456) ∨ (¬ p1211) ∨ (¬ p1256)) : (¬ p1211) ∨ p455 ∨ p422 ∨ (¬ p134) ∨ (¬ p23) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p455) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p23 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19388 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u6)

theorem step31314 (p3 p5 p23 p134 p163 p226 p227 p455 p456 p498 : Prop)
    (h26871 : p456 ∨ p455)
    (h26847 : p226 ∨ p3)
    (h18993 : (¬ p5) ∨ (¬ p23) ∨ (¬ p134) ∨ (¬ p163) ∨ (¬ p226) ∨ (¬ p227) ∨ (¬ p456) ∨ (¬ p498)) : p455 ∨ (¬ p227) ∨ (¬ p163) ∨ (¬ p5) ∨ (¬ p134) ∨ (¬ p498) ∨ p3 ∨ (¬ p23) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p23 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18993 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u5)

theorem step31315 (p3 p5 p23 p125 p134 p163 p226 p362 p420 p498 : Prop)
    (h26847 : p226 ∨ p3)
    (h26865 : p362 ∨ p125)
    (h19432 : (¬ p5) ∨ (¬ p23) ∨ (¬ p134) ∨ (¬ p163) ∨ (¬ p226) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p498)) : (¬ p420) ∨ p3 ∨ (¬ p5) ∨ (¬ p134) ∨ (¬ p498) ∨ (¬ p23) ∨ p125 ∨ (¬ p163) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p23 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19432 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u4)

theorem step31316 (p23 p101 p102 p344 p634 p897 : Prop)
    (h26837 : p102 ∨ p101)
    (h17216 : (¬ p23) ∨ (¬ p102) ∨ (¬ p344) ∨ (¬ p634) ∨ (¬ p897)) : (¬ p344) ∨ (¬ p634) ∨ p101 ∨ (¬ p897) ∨ (¬ p23) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p634 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p23 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17216 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)

theorem step31317 (p15 p22 p125 p420 p494 p601 : Prop)
    (h26881 : p601 ∨ p420)
    (h18508 : (¬ p15) ∨ (¬ p22) ∨ (¬ p125) ∨ (¬ p494) ∨ (¬ p601)) : (¬ p15) ∨ (¬ p125) ∨ p420 ∨ (¬ p22) ∨ (¬ p494) := by
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
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p22 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18508 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)

theorem step31319 (p15 p22 p125 p126 p258 p288 p301 p362 p421 p897 p1096 p1099 : Prop)
    (h26857 : p301 ∨ p126)
    (h26913 : p1099 ∨ p1096)
    (h26865 : p362 ∨ p125)
    (h26855 : p288 ∨ p258)
    (h16455 : (¬ p15) ∨ (¬ p22) ∨ (¬ p288) ∨ (¬ p301) ∨ (¬ p362) ∨ (¬ p421) ∨ (¬ p897) ∨ (¬ p1099)) : p126 ∨ (¬ p15) ∨ (¬ p22) ∨ (¬ p421) ∨ p1096 ∨ p125 ∨ p258 ∨ (¬ p897) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p22 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u11 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h16455 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u9)

theorem step31320 (p16 p17 p980 p983 p1095 p1096 p1454 p1644 : Prop)
    (h26903 : p983 ∨ p980)
    (h20591 : (¬ p16) ∨ (¬ p17) ∨ (¬ p983) ∨ (¬ p1095) ∨ (¬ p1096) ∨ (¬ p1454) ∨ (¬ p1644)) : (¬ p1644) ∨ (¬ p1454) ∨ (¬ p17) ∨ p980 ∨ (¬ p16) ∨ (¬ p1095) ∨ (¬ p1096) := by
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
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p16 := by
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
  have u7 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20591 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u0)

theorem step31321 (p16 p161 p228 p532 p789 p790 p814 p858 p1225 p1229 : Prop)
    (h26925 : p1225 ∨ p161)
    (h26897 : p858 ∨ p789)
    (h26893 : p814 ∨ p790)
    (h19922 : (¬ p16) ∨ (¬ p228) ∨ (¬ p532) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1225) ∨ (¬ p1229)) : p161 ∨ (¬ p1229) ∨ p789 ∨ (¬ p16) ∨ (¬ p228) ∨ p790 ∨ (¬ p532) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p161) := fun hu => hn (Or.inl hu)
  have u1 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19922 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step31322 (p16 p161 p665 p789 p790 p814 p858 p980 p1096 p1225 p1311 : Prop)
    (h26925 : p1225 ∨ p161)
    (h26893 : p814 ∨ p790)
    (h26897 : p858 ∨ p789)
    (h19201 : (¬ p16) ∨ (¬ p665) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p980) ∨ (¬ p1096) ∨ (¬ p1225) ∨ (¬ p1311)) : p161 ∨ (¬ p1311) ∨ (¬ p16) ∨ p790 ∨ p789 ∨ (¬ p665) ∨ (¬ p980) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p161) := fun hu => hn (Or.inl hu)
  have u1 : p1311 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1225 := by
    rcases h26925 with q0 | q1
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
  rcases h19201 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u1)

theorem step31323 (p16 p533 p789 p790 p814 p858 p1096 p1325 p1562 : Prop)
    (h26897 : p858 ∨ p789)
    (h26893 : p814 ∨ p790)
    (h18445 : (¬ p16) ∨ (¬ p533) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1096) ∨ (¬ p1325) ∨ (¬ p1562)) : (¬ p1562) ∨ (¬ p1096) ∨ p789 ∨ (¬ p16) ∨ (¬ p1325) ∨ (¬ p533) ∨ p790 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1562 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18445 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u0)

theorem step31324 (p15 p16 p18 p19 p101 p102 p789 p790 p814 p858 p1325 : Prop)
    (h26837 : p102 ∨ p101)
    (h26897 : p858 ∨ p789)
    (h26893 : p814 ∨ p790)
    (h26829 : p19 ∨ p18)
    (h17870 : (¬ p15) ∨ (¬ p16) ∨ (¬ p19) ∨ (¬ p102) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1325)) : (¬ p15) ∨ p101 ∨ (¬ p1325) ∨ (¬ p16) ∨ p789 ∨ p790 ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p101) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h17870 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u2)

theorem step31325 (p15 p16 p224 p234 p542 p657 p789 p790 p814 p858 : Prop)
    (h26887 : p657 ∨ p224)
    (h26897 : p858 ∨ p789)
    (h26893 : p814 ∨ p790)
    (h19085 : (¬ p15) ∨ (¬ p16) ∨ (¬ p234) ∨ (¬ p542) ∨ (¬ p657) ∨ (¬ p814) ∨ (¬ p858)) : p224 ∨ (¬ p15) ∨ p789 ∨ (¬ p234) ∨ p790 ∨ (¬ p16) ∨ (¬ p542) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p224) := fun hu => hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19085 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u8)

theorem step31326 (p16 p17 p595 p1286 p1325 p1333 p1454 p1644 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h19885 : (¬ p16) ∨ (¬ p17) ∨ (¬ p595) ∨ (¬ p1286) ∨ (¬ p1333) ∨ (¬ p1454) ∨ (¬ p1644)) : (¬ p1644) ∨ (¬ p1454) ∨ (¬ p16) ∨ (¬ p595) ∨ (¬ p17) ∨ p1325 ∨ (¬ p1286) := by
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
  have u2 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19885 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u0)

theorem step31327 (p15 p16 p18 p19 p121 p228 p789 p790 p814 p858 : Prop)
    (h26893 : p814 ∨ p790)
    (h26897 : p858 ∨ p789)
    (h26829 : p19 ∨ p18)
    (h17875 : (¬ p15) ∨ (¬ p16) ∨ (¬ p19) ∨ (¬ p121) ∨ (¬ p228) ∨ (¬ p814) ∨ (¬ p858)) : (¬ p15) ∨ (¬ p121) ∨ (¬ p228) ∨ p790 ∨ p789 ∨ p18 ∨ (¬ p16) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17875 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u8)

theorem step31328 (p16 p303 p351 p387 p789 p790 p814 p858 p897 p904 p1096 : Prop)
    (h26899 : p904 ∨ p897)
    (h26867 : p387 ∨ p303)
    (h26893 : p814 ∨ p790)
    (h26897 : p858 ∨ p789)
    (h19596 : (¬ p16) ∨ (¬ p351) ∨ (¬ p387) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p904) ∨ (¬ p1096)) : (¬ p1096) ∨ p897 ∨ p303 ∨ (¬ p16) ∨ (¬ p351) ∨ p790 ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p897) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19596 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u0)

theorem step31329 (p2 p16 p188 p303 p351 p387 p419 p897 p904 p1096 : Prop)
    (h26899 : p904 ∨ p897)
    (h26867 : p387 ∨ p303)
    (h19129 : (¬ p2) ∨ (¬ p16) ∨ (¬ p188) ∨ (¬ p351) ∨ (¬ p387) ∨ (¬ p419) ∨ (¬ p904) ∨ (¬ p1096)) : (¬ p2) ∨ (¬ p1096) ∨ p897 ∨ (¬ p351) ∨ (¬ p419) ∨ (¬ p188) ∨ p303 ∨ (¬ p16) := by
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
  have u2 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19129 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u1)

theorem step31331 (p16 p189 p344 p422 p495 p499 p633 p1465 : Prop)
    (h26875 : p499 ∨ p495)
    (h19789 : (¬ p16) ∨ (¬ p189) ∨ (¬ p344) ∨ (¬ p422) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p1465)) : (¬ p344) ∨ (¬ p633) ∨ (¬ p16) ∨ p495 ∨ (¬ p422) ∨ (¬ p189) ∨ (¬ p1465) := by
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
  have u2 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19789 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u6)

theorem step31332 (p9 p16 p789 p790 p814 p858 p903 p1055 p1061 p1074 p1542 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h26897 : p858 ∨ p789)
    (h26893 : p814 ∨ p790)
    (h26119 : (¬ p903) ∨ (¬ p1542) ∨ (¬ p16) ∨ (¬ p1061) ∨ (¬ p1074) ∨ (¬ p858) ∨ (¬ p9) ∨ (¬ p814)) : (¬ p1542) ∨ p1055 ∨ (¬ p16) ∨ (¬ p903) ∨ p789 ∨ (¬ p1074) ∨ (¬ p9) ∨ p790 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p903 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p9 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h26119 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u10)

theorem step31333 (p12 p14 p15 p16 p665 p789 p790 p814 p858 : Prop)
    (h26893 : p814 ∨ p790)
    (h26897 : p858 ∨ p789)
    (h19204 : (¬ p12) ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p16) ∨ (¬ p665) ∨ (¬ p814) ∨ (¬ p858)) : (¬ p12) ∨ (¬ p14) ∨ (¬ p16) ∨ (¬ p665) ∨ (¬ p15) ∨ p790 ∨ p789 := by
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
  have u2 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u8 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19204 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u8)

theorem step31335 (p10 p16 p134 p189 p351 p897 p904 p1096 : Prop)
    (h26899 : p904 ∨ p897)
    (h18940 : (¬ p10) ∨ (¬ p16) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p351) ∨ (¬ p904) ∨ (¬ p1096)) : (¬ p1096) ∨ (¬ p10) ∨ p897 ∨ (¬ p189) ∨ (¬ p351) ∨ (¬ p134) ∨ (¬ p16) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18940 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u0)

theorem step31336 (p16 p161 p185 p734 p836 p1225 p1229 p1335 : Prop)
    (h26925 : p1225 ∨ p161)
    (h19063 : (¬ p16) ∨ (¬ p185) ∨ (¬ p734) ∨ (¬ p836) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1335)) : p161 ∨ (¬ p836) ∨ (¬ p185) ∨ (¬ p1229) ∨ (¬ p16) ∨ (¬ p734) ∨ (¬ p1335) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p161) := fun hu => hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p734 := by
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
    · exact False.elim (u0 q1)
  rcases h19063 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step31337 (p14 p15 p16 p185 p225 p544 p664 p1115 : Prop)
    (h26877 : p544 ∨ p225)
    (h18807 : (¬ p14) ∨ (¬ p15) ∨ (¬ p16) ∨ (¬ p185) ∨ (¬ p544) ∨ (¬ p664) ∨ (¬ p1115)) : (¬ p1115) ∨ (¬ p14) ∨ (¬ p664) ∨ (¬ p16) ∨ (¬ p185) ∨ (¬ p15) ∨ p225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p664 := by
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
  have u5 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18807 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u0)

theorem step31338 (p15 p16 p423 p790 p814 p1015 p1035 p1335 : Prop)
    (h26893 : p814 ∨ p790)
    (h19173 : (¬ p15) ∨ (¬ p16) ∨ (¬ p423) ∨ (¬ p814) ∨ (¬ p1015) ∨ (¬ p1035) ∨ (¬ p1335)) : (¬ p1035) ∨ (¬ p423) ∨ p790 ∨ (¬ p15) ∨ (¬ p1015) ∨ (¬ p1335) ∨ (¬ p16) := by
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
  have u2 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p15 := by
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
  have u6 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19173 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u5)

theorem step31339 (p16 p161 p163 p167 p189 p940 p985 p1225 p1229 : Prop)
    (h26925 : p1225 ∨ p161)
    (h26843 : p167 ∨ p163)
    (h17935 : (¬ p16) ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1225) ∨ (¬ p1229)) : p161 ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p189) ∨ (¬ p1229) ∨ p163 ∨ (¬ p16) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p161) := fun hu => hn (Or.inl hu)
  have u1 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17935 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u4)

theorem step31340 (p16 p17 p161 p258 p726 p985 p1225 p1229 : Prop)
    (h26925 : p1225 ∨ p161)
    (h17933 : (¬ p16) ∨ (¬ p17) ∨ (¬ p258) ∨ (¬ p726) ∨ (¬ p985) ∨ (¬ p1225) ∨ (¬ p1229)) : p161 ∨ (¬ p985) ∨ (¬ p258) ∨ (¬ p726) ∨ (¬ p16) ∨ (¬ p1229) ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p161) := fun hu => hn (Or.inl hu)
  have u1 : p985 := by
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
  have u4 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17933 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u5)

theorem step31341 (p16 p17 p258 p664 p897 p904 p1076 p1096 : Prop)
    (h26899 : p904 ∨ p897)
    (h19333 : (¬ p16) ∨ (¬ p17) ∨ (¬ p258) ∨ (¬ p664) ∨ (¬ p904) ∨ (¬ p1076) ∨ (¬ p1096)) : (¬ p258) ∨ (¬ p1076) ∨ p897 ∨ (¬ p17) ∨ (¬ p16) ∨ (¬ p664) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p664 := by
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
  rcases h19333 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u6)

theorem step31342 (p16 p17 p258 p344 p346 p738 p1096 p1562 : Prop)
    (h26863 : p346 ∨ p344)
    (h20034 : (¬ p16) ∨ (¬ p17) ∨ (¬ p258) ∨ (¬ p346) ∨ (¬ p738) ∨ (¬ p1096) ∨ (¬ p1562)) : (¬ p1562) ∨ (¬ p738) ∨ p344 ∨ (¬ p258) ∨ (¬ p1096) ∨ (¬ p16) ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1562 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p738 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20034 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u0)

theorem step31343 (p16 p17 p258 p344 p346 p668 p1095 p1096 : Prop)
    (h26863 : p346 ∨ p344)
    (h20508 : (¬ p16) ∨ (¬ p17) ∨ (¬ p258) ∨ (¬ p346) ∨ (¬ p668) ∨ (¬ p1095) ∨ (¬ p1096)) : (¬ p258) ∨ (¬ p1096) ∨ (¬ p16) ∨ p344 ∨ (¬ p17) ∨ (¬ p1095) ∨ (¬ p668) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20508 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u1)

theorem step31344 (p15 p16 p17 p234 p258 p344 p346 p542 : Prop)
    (h26863 : p346 ∨ p344)
    (h20111 : (¬ p15) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p234) ∨ (¬ p258) ∨ (¬ p346) ∨ (¬ p542)) : (¬ p258) ∨ p344 ∨ (¬ p15) ∨ (¬ p17) ∨ (¬ p16) ∨ (¬ p542) ∨ (¬ p234) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20111 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u5)

theorem step31345 (p11 p15 p16 p17 p234 p389 p419 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h20547 : (¬ p11) ∨ (¬ p15) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p234) ∨ (¬ p389) ∨ (¬ p996)) : (¬ p11) ∨ (¬ p389) ∨ (¬ p16) ∨ (¬ p15) ∨ (¬ p234) ∨ p419 ∨ (¬ p17) := by
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
  have u2 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20547 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step31346 (p13 p86 p455 p456 p495 p980 p1346 p1508 : Prop)
    (h26871 : p456 ∨ p455)
    (h17274 : (¬ p13) ∨ (¬ p86) ∨ (¬ p456) ∨ (¬ p495) ∨ (¬ p980) ∨ (¬ p1346) ∨ (¬ p1508)) : p455 ∨ (¬ p1508) ∨ (¬ p1346) ∨ (¬ p980) ∨ (¬ p13) ∨ (¬ p86) ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17274 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u1)

theorem step31347 (p8 p12 p13 p225 p455 p456 p495 : Prop)
    (h26871 : p456 ∨ p455)
    (h22762 : (¬ p225) ∨ (¬ p8) ∨ (¬ p495) ∨ (¬ p12) ∨ (¬ p13) ∨ (¬ p456)) : p455 ∨ (¬ p13) ∨ (¬ p225) ∨ (¬ p12) ∨ (¬ p495) ∨ (¬ p8) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h22762 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u6)

theorem step31349 (p11 p13 p17 p156 p161 p189 p193 p923 p980 p1225 p1311 : Prop)
    (h26845 : p193 ∨ p189)
    (h26925 : p1225 ∨ p161)
    (h20026 : (¬ p11) ∨ (¬ p13) ∨ (¬ p17) ∨ (¬ p156) ∨ (¬ p193) ∨ (¬ p923) ∨ (¬ p980) ∨ (¬ p1225) ∨ (¬ p1311)) : (¬ p1311) ∨ (¬ p11) ∨ (¬ p156) ∨ (¬ p923) ∨ (¬ p980) ∨ (¬ p13) ∨ p189 ∨ p161 ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1311 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p11 := by
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
  have u4 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p161) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h20026 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u0)

theorem step31351 (p6 p8 p9 p13 p41 p45 p121 p192 p897 p1095 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26831 : p45 ∨ p41)
    (h18402 : (¬ p6) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p13) ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p897) ∨ (¬ p1095) ∨ (¬ p1206)) : p121 ∨ (¬ p13) ∨ (¬ p1095) ∨ (¬ p897) ∨ (¬ p6) ∨ p41 ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p192) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p9 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18402 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u2)
  · exact False.elim (q8 u9)

theorem step31352 (p3 p12 p17 p190 p980 p983 p1454 p1644 : Prop)
    (h26903 : p983 ∨ p980)
    (h17662 : (¬ p3) ∨ (¬ p12) ∨ (¬ p17) ∨ (¬ p190) ∨ (¬ p983) ∨ (¬ p1454) ∨ (¬ p1644)) : (¬ p12) ∨ (¬ p3) ∨ p980 ∨ (¬ p1454) ∨ (¬ p1644) ∨ (¬ p17) ∨ (¬ p190) := by
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
  have u2 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1454 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1644 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17662 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)

theorem step31355 (p3 p12 p17 p190 p258 p344 p346 p668 : Prop)
    (h26863 : p346 ∨ p344)
    (h20465 : (¬ p3) ∨ (¬ p12) ∨ (¬ p17) ∨ (¬ p190) ∨ (¬ p258) ∨ (¬ p346) ∨ (¬ p668)) : (¬ p258) ∨ (¬ p12) ∨ (¬ p17) ∨ (¬ p3) ∨ (¬ p190) ∨ (¬ p668) ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
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
  have u3 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20465 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u5)

theorem step31359 (p12 p84 p163 p189 p193 p495 p499 p582 p1229 p1232 p1313 : Prop)
    (h26875 : p499 ∨ p495)
    (h26927 : p1232 ∨ p1229)
    (h26845 : p193 ∨ p189)
    (h18748 : (¬ p12) ∨ (¬ p84) ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p499) ∨ (¬ p582) ∨ (¬ p1232) ∨ (¬ p1313)) : p495 ∨ p1229 ∨ (¬ p163) ∨ (¬ p582) ∨ (¬ p12) ∨ p189 ∨ (¬ p84) ∨ (¬ p1313) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p495) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1313 := by
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
    · exact False.elim (u1 q1)
  have u10 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18748 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u7)

theorem step31360 (p12 p84 p163 p189 p193 p595 p1229 p1232 p1313 p1394 : Prop)
    (h26845 : p193 ∨ p189)
    (h26927 : p1232 ∨ p1229)
    (h18773 : (¬ p12) ∨ (¬ p84) ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p595) ∨ (¬ p1232) ∨ (¬ p1313) ∨ (¬ p1394)) : (¬ p1394) ∨ (¬ p84) ∨ p189 ∨ p1229 ∨ (¬ p1313) ∨ (¬ p163) ∨ (¬ p595) ∨ (¬ p12) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1394 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1313 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18773 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u0)

theorem step31361 (p12 p124 p225 p304 p1076 : Prop)
    (h26859 : p304 ∨ p124)
    (h19781 : (¬ p12) ∨ (¬ p225) ∨ (¬ p304) ∨ (¬ p1076)) : (¬ p1076) ∨ p124 ∨ (¬ p225) ∨ (¬ p12) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19781 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step31362 (p12 p108 p124 p209 p304 p1076 : Prop)
    (h26859 : p304 ∨ p124)
    (h19823 : (¬ p12) ∨ (¬ p108) ∨ (¬ p209) ∨ (¬ p304) ∨ (¬ p1076)) : (¬ p1076) ∨ p124 ∨ (¬ p12) ∨ (¬ p108) ∨ (¬ p209) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19823 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)

theorem step31364 (p12 p17 p126 p225 p243 p256 p347 p1055 : Prop)
    (h26853 : p256 ∨ p17)
    (h16685 : (¬ p12) ∨ (¬ p126) ∨ (¬ p225) ∨ (¬ p243) ∨ (¬ p256) ∨ (¬ p347) ∨ (¬ p1055)) : (¬ p1055) ∨ (¬ p347) ∨ (¬ p126) ∨ p17 ∨ (¬ p243) ∨ (¬ p12) ∨ (¬ p225) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p243 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16685 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u0)

theorem step31367 (p3 p12 p17 p135 p187 p256 p980 p983 p1516 p1751 : Prop)
    (h26853 : p256 ∨ p17)
    (h26903 : p983 ∨ p980)
    (h17667 : (¬ p3) ∨ (¬ p12) ∨ (¬ p135) ∨ (¬ p187) ∨ (¬ p256) ∨ (¬ p983) ∨ (¬ p1516) ∨ (¬ p1751)) : (¬ p1516) ∨ (¬ p1751) ∨ (¬ p135) ∨ (¬ p187) ∨ p17 ∨ p980 ∨ (¬ p3) ∨ (¬ p12) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1516 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1751 := by
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
  have u4 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17667 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u1)

theorem step31368 (p3 p12 p41 p87 p187 p665 p789 p790 p814 p858 : Prop)
    (h26897 : p858 ∨ p789)
    (h26893 : p814 ∨ p790)
    (h16275 : (¬ p3) ∨ (¬ p12) ∨ (¬ p41) ∨ (¬ p87) ∨ (¬ p187) ∨ (¬ p665) ∨ (¬ p814) ∨ (¬ p858)) : (¬ p41) ∨ (¬ p3) ∨ (¬ p665) ∨ (¬ p87) ∨ p789 ∨ (¬ p12) ∨ (¬ p187) ∨ p790 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h16275 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u8)

theorem step31369 (p3 p12 p190 p258 p261 p980 p983 p1624 p1651 : Prop)
    (h26903 : p983 ∨ p980)
    (h17661 : (¬ p3) ∨ (¬ p12) ∨ (¬ p190) ∨ (¬ p258) ∨ (¬ p261) ∨ (¬ p983) ∨ (¬ p1624) ∨ (¬ p1651)) : (¬ p1651) ∨ (¬ p1624) ∨ (¬ p12) ∨ (¬ p258) ∨ (¬ p261) ∨ (¬ p3) ∨ (¬ p190) ∨ p980 := by
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
  have u2 : p12 := by
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
  have u5 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h17661 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u0)

theorem step31370 (p3 p12 p13 p41 p125 p187 p420 p455 p456 p494 p601 : Prop)
    (h26871 : p456 ∨ p455)
    (h26881 : p601 ∨ p420)
    (h18786 : (¬ p3) ∨ (¬ p12) ∨ (¬ p13) ∨ (¬ p41) ∨ (¬ p125) ∨ (¬ p187) ∨ (¬ p456) ∨ (¬ p494) ∨ (¬ p601)) : p455 ∨ p420 ∨ (¬ p187) ∨ (¬ p13) ∨ (¬ p3) ∨ (¬ p12) ∨ (¬ p125) ∨ (¬ p41) ∨ (¬ p494) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p420) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18786 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u10)

theorem step31371 (p3 p12 p71 p897 p904 p1074 : Prop)
    (h26899 : p904 ∨ p897)
    (h19117 : (¬ p3) ∨ (¬ p12) ∨ (¬ p71) ∨ (¬ p904) ∨ (¬ p1074)) : (¬ p12) ∨ (¬ p3) ∨ p897 ∨ (¬ p1074) ∨ (¬ p71) := by
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
  have u2 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19117 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)

theorem step31372 (p3 p12 p41 p187 p980 p983 : Prop)
    (h26903 : p983 ∨ p980)
    (h19242 : (¬ p3) ∨ (¬ p12) ∨ (¬ p41) ∨ (¬ p187) ∨ (¬ p983)) : (¬ p12) ∨ (¬ p3) ∨ (¬ p41) ∨ (¬ p187) ∨ p980 := by
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
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19242 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)

theorem step31373 (p3 p12 p41 p187 p494 p532 p665 p961 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h19246 : (¬ p3) ∨ (¬ p12) ∨ (¬ p41) ∨ (¬ p187) ∨ (¬ p494) ∨ (¬ p532) ∨ (¬ p665) ∨ (¬ p961) ∨ (¬ p1333)) : (¬ p41) ∨ (¬ p961) ∨ (¬ p532) ∨ (¬ p12) ∨ (¬ p187) ∨ (¬ p665) ∨ (¬ p3) ∨ (¬ p494) ∨ p1325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h19246 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u9)

theorem step31374 (p3 p6 p12 p134 p142 : Prop)
    (h26841 : p142 ∨ p134)
    (h19372 : (¬ p3) ∨ (¬ p6) ∨ (¬ p12) ∨ (¬ p142)) : (¬ p3) ∨ (¬ p12) ∨ (¬ p6) ∨ p134 := by
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
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19372 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)

theorem step31375 (p12 p185 p225 p237 p836 p840 : Prop)
    (h26851 : p237 ∨ p185)
    (h26895 : p840 ∨ p836)
    (h17204 : (¬ p12) ∨ (¬ p225) ∨ (¬ p237) ∨ (¬ p840)) : (¬ p12) ∨ (¬ p225) ∨ p185 ∨ p836 := by
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
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17204 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step31376 (p12 p163 p189 p193 p980 p983 : Prop)
    (h26903 : p983 ∨ p980)
    (h26845 : p193 ∨ p189)
    (h18757 : (¬ p12) ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p983)) : p980 ∨ (¬ p12) ∨ (¬ p163) ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18757 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step31377 (p6 p12 p140 p163 p191 p258 p344 p346 p668 : Prop)
    (h26863 : p346 ∨ p344)
    (h19370 : (¬ p6) ∨ (¬ p12) ∨ (¬ p140) ∨ (¬ p163) ∨ (¬ p191) ∨ (¬ p258) ∨ (¬ p346) ∨ (¬ p668)) : (¬ p258) ∨ p344 ∨ (¬ p163) ∨ (¬ p6) ∨ (¬ p668) ∨ (¬ p191) ∨ (¬ p140) ∨ (¬ p12) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19370 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u4)

theorem step31378 (p12 p110 p125 p126 p194 p258 p266 p288 p301 p362 p556 p1055 : Prop)
    (h26857 : p301 ∨ p126)
    (h26855 : p288 ∨ p258)
    (h26865 : p362 ∨ p125)
    (h19492 : (¬ p12) ∨ (¬ p110) ∨ (¬ p194) ∨ (¬ p266) ∨ (¬ p288) ∨ (¬ p301) ∨ (¬ p362) ∨ (¬ p556) ∨ (¬ p1055)) : p126 ∨ (¬ p1055) ∨ (¬ p12) ∨ p258 ∨ (¬ p194) ∨ (¬ p266) ∨ (¬ p110) ∨ p125 ∨ (¬ p556) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p556 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h19492 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u11)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u1)

theorem step31379 (p12 p185 p189 p193 p1115 : Prop)
    (h26845 : p193 ∨ p189)
    (h18303 : (¬ p12) ∨ (¬ p185) ∨ (¬ p193) ∨ (¬ p1115)) : (¬ p12) ∨ (¬ p1115) ∨ (¬ p185) ∨ p189 := by
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
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18303 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)

theorem step31382 (p8 p419 p435 p728 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h20540 : (¬ p8) ∨ (¬ p435) ∨ (¬ p728) ∨ (¬ p996)) : p419 ∨ (¬ p728) ∨ (¬ p435) ∨ (¬ p8) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h20540 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)

theorem step31383 (p8 p258 p288 p1055 p1076 p1077 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26855 : p288 ∨ p258)
    (h19003 : (¬ p8) ∨ (¬ p288) ∨ (¬ p1055) ∨ (¬ p1077)) : (¬ p1055) ∨ p1076 ∨ (¬ p8) ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19003 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)

theorem step31384 (p8 p224 p262 p310 p576 p581 p657 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26879 : p581 ∨ p576)
    (h26887 : p657 ∨ p224)
    (h18391 : (¬ p8) ∨ (¬ p262) ∨ (¬ p310) ∨ (¬ p581) ∨ (¬ p657) ∨ (¬ p1333)) : p1325 ∨ (¬ p8) ∨ (¬ p262) ∨ (¬ p310) ∨ p576 ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1325) := fun hu => hn (Or.inl hu)
  have u1 : p8 := by
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
  have u4 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u8 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18391 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u6)

theorem step31385 (p6 p8 p18 p19 p64 p224 p234 p657 p1187 p1325 p1333 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26829 : p19 ∨ p18)
    (h26931 : p1333 ∨ p1325)
    (h26887 : p657 ∨ p224)
    (h22763 : (¬ p8) ∨ (¬ p1187) ∨ (¬ p6) ∨ (¬ p19) ∨ (¬ p657) ∨ (¬ p64) ∨ (¬ p1333)) : p234 ∨ p18 ∨ (¬ p64) ∨ (¬ p8) ∨ p1325 ∨ p224 ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p18) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h22763 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u9)

theorem step31387 (p8 p244 p918 p928 p1385 : Prop)
    (h26901 : p928 ∨ p918)
    (h26787 : (¬ p1385) ∨ (¬ p8) ∨ (¬ p928) ∨ (¬ p244)) : (¬ p8) ∨ p918 ∨ (¬ p1385) ∨ (¬ p244) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p244 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h26787 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)

theorem step31388 (p8 p158 p836 p840 : Prop)
    (h26894 : (¬ p836) ∨ (¬ p840))
    (h12015 : (¬ p8) ∨ (¬ p158) ∨ p840) : (¬ p8) ∨ (¬ p836) ∨ (¬ p158) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p840) := by
    rcases h26894 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h12015 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (u3 q2)

theorem step31390 (p8 p158 p344 p346 p918 p928 p1076 p1077 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26901 : p928 ∨ p918)
    (h26863 : p346 ∨ p344)
    (h21022 : (¬ p158) ∨ (¬ p8) ∨ (¬ p346) ∨ (¬ p928) ∨ (¬ p1077)) : (¬ p8) ∨ p1076 ∨ (¬ p158) ∨ p918 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h21022 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step31391 (p8 p306 p344 p346 : Prop)
    (h26863 : p346 ∨ p344)
    (h13993 : (¬ p8) ∨ (¬ p306) ∨ (¬ p346)) : (¬ p306) ∨ (¬ p8) ∨ p344 := by
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
  have u3 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h13993 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)

theorem step31392 (p8 p101 p344 p346 p1055 : Prop)
    (h26863 : p346 ∨ p344)
    (h19299 : (¬ p8) ∨ (¬ p101) ∨ (¬ p346) ∨ (¬ p1055)) : (¬ p1055) ∨ (¬ p101) ∨ p344 ∨ (¬ p8) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19299 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step31395 (p8 p89 p189 p193 p225 p306 p1040 p1076 p1250 p1465 p1508 : Prop)
    (h26845 : p193 ∨ p189)
    (h19354 : (¬ p8) ∨ (¬ p89) ∨ (¬ p193) ∨ (¬ p225) ∨ (¬ p306) ∨ (¬ p1040) ∨ (¬ p1076) ∨ (¬ p1250) ∨ (¬ p1465) ∨ (¬ p1508)) : (¬ p306) ∨ (¬ p1508) ∨ (¬ p89) ∨ (¬ p8) ∨ (¬ p1076) ∨ p189 ∨ (¬ p225) ∨ (¬ p1040) ∨ (¬ p1250) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1040 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1250 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19354 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u9)
  · exact False.elim (q9 u1)

theorem step31397 (p8 p163 p191 p557 p728 p1140 p1159 p1330 p1465 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h18436 : (¬ p8) ∨ (¬ p163) ∨ (¬ p191) ∨ (¬ p557) ∨ (¬ p728) ∨ (¬ p1159) ∨ (¬ p1330) ∨ (¬ p1465)) : (¬ p728) ∨ (¬ p557) ∨ (¬ p1330) ∨ (¬ p1465) ∨ (¬ p163) ∨ (¬ p191) ∨ p1140 ∨ (¬ p8) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18436 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u3)

theorem step31398 (p8 p135 p187 p561 p576 p581 p897 p922 : Prop)
    (h26879 : p581 ∨ p576)
    (h20519 : (¬ p8) ∨ (¬ p135) ∨ (¬ p187) ∨ (¬ p561) ∨ (¬ p581) ∨ (¬ p897) ∨ (¬ p922)) : (¬ p8) ∨ (¬ p561) ∨ (¬ p135) ∨ (¬ p897) ∨ (¬ p922) ∨ p576 ∨ (¬ p187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p135 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20519 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)

theorem step31399 (p8 p15 p18 p69 p101 p224 p657 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26833 : p69 ∨ p15)
    (h26887 : p657 ∨ p224)
    (h22764 : (¬ p657) ∨ (¬ p8) ∨ (¬ p1333) ∨ (¬ p18) ∨ (¬ p69) ∨ (¬ p101)) : p1325 ∨ (¬ p101) ∨ (¬ p8) ∨ p15 ∨ (¬ p18) ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1325) := fun hu => hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h22764 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u1)

theorem step31400 (p8 p15 p18 p69 p121 p224 p389 p657 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26833 : p69 ∨ p15)
    (h26887 : p657 ∨ p224)
    (h22765 : (¬ p389) ∨ (¬ p69) ∨ (¬ p1206) ∨ (¬ p18) ∨ (¬ p8) ∨ (¬ p657)) : p121 ∨ (¬ p389) ∨ (¬ p18) ∨ p15 ∨ p224 ∨ (¬ p8) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h22765 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u8)

theorem step31402 (p8 p14 p15 p63 p69 p110 p229 p310 p344 p346 p421 p577 : Prop)
    (h26849 : p229 ∨ p14)
    (h26833 : p69 ∨ p15)
    (h26863 : p346 ∨ p344)
    (h19477 : (¬ p8) ∨ (¬ p63) ∨ (¬ p69) ∨ (¬ p110) ∨ (¬ p229) ∨ (¬ p310) ∨ (¬ p346) ∨ (¬ p421) ∨ (¬ p577)) : p14 ∨ p15 ∨ (¬ p310) ∨ (¬ p577) ∨ (¬ p421) ∨ p344 ∨ (¬ p63) ∨ (¬ p110) ∨ (¬ p8) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u11 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19477 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u11)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u3)

theorem step31404 (p6 p8 p14 p18 p19 p64 p86 p168 p229 p242 p836 : Prop)
    (h26849 : p229 ∨ p14)
    (h26829 : p19 ∨ p18)
    (h18694 : (¬ p6) ∨ (¬ p8) ∨ (¬ p19) ∨ (¬ p64) ∨ (¬ p86) ∨ (¬ p168) ∨ (¬ p229) ∨ (¬ p242) ∨ (¬ p836)) : (¬ p168) ∨ p14 ∨ (¬ p242) ∨ (¬ p64) ∨ (¬ p836) ∨ (¬ p86) ∨ (¬ p6) ∨ p18 ∨ (¬ p8) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p168 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p14) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h18694 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u2)
  · exact False.elim (q8 u4)

theorem step31405 (p6 p8 p18 p19 p64 p224 p389 p423 p657 p1141 p1208 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26829 : p19 ∨ p18)
    (h26887 : p657 ∨ p224)
    (h22766 : (¬ p1208) ∨ (¬ p8) ∨ (¬ p6) ∨ (¬ p19) ∨ (¬ p389) ∨ (¬ p657) ∨ (¬ p64) ∨ (¬ p1141)) : (¬ p1208) ∨ (¬ p389) ∨ p423 ∨ (¬ p8) ∨ (¬ p6) ∨ (¬ p64) ∨ p18 ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1208 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p423) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h22766 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u8)

theorem step31406 (p8 p9 p63 p85 p897 p929 : Prop)
    (h26835 : p85 ∨ p63)
    (h16393 : (¬ p8) ∨ (¬ p9) ∨ (¬ p85) ∨ (¬ p897) ∨ (¬ p929)) : (¬ p897) ∨ (¬ p929) ∨ p63 ∨ (¬ p8) ∨ (¬ p9) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p9 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16393 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)

theorem step31407 (p8 p225 p544 p557 : Prop)
    (h26876 : (¬ p225) ∨ (¬ p544))
    (h9322 : (¬ p8) ∨ p544 ∨ (¬ p557)) : (¬ p557) ∨ (¬ p8) ∨ (¬ p225) := by
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
  have u3 : (¬ p544) := by
    rcases h26876 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h9322 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u0)

theorem step31410 (p6 p8 p18 p19 p48 p344 p346 p561 : Prop)
    (h26863 : p346 ∨ p344)
    (h26829 : p19 ∨ p18)
    (h18835 : (¬ p6) ∨ (¬ p8) ∨ (¬ p19) ∨ (¬ p48) ∨ (¬ p346) ∨ (¬ p561)) : (¬ p561) ∨ (¬ p48) ∨ p344 ∨ (¬ p6) ∨ (¬ p8) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18835 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u0)

theorem step31411 (p8 p17 p41 p45 p158 p258 p664 p918 p928 p1076 : Prop)
    (h26831 : p45 ∨ p41)
    (h26901 : p928 ∨ p918)
    (h19337 : (¬ p8) ∨ (¬ p17) ∨ (¬ p45) ∨ (¬ p158) ∨ (¬ p258) ∨ (¬ p664) ∨ (¬ p928) ∨ (¬ p1076)) : (¬ p258) ∨ (¬ p1076) ∨ (¬ p664) ∨ p41 ∨ p918 ∨ (¬ p17) ∨ (¬ p158) ∨ (¬ p8) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19337 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u1)

theorem step31412 (p8 p17 p83 p172 p225 p576 p581 p918 : Prop)
    (h26879 : p581 ∨ p576)
    (h22767 : (¬ p172) ∨ (¬ p225) ∨ (¬ p8) ∨ (¬ p17) ∨ (¬ p83) ∨ (¬ p581) ∨ (¬ p918)) : p576 ∨ (¬ p225) ∨ (¬ p17) ∨ (¬ p918) ∨ (¬ p83) ∨ (¬ p8) ∨ (¬ p172) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p576) := fun hu => hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
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
  have u5 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p172 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h22767 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step31413 (p8 p17 p83 p224 p576 p581 p657 p864 p1249 : Prop)
    (h26887 : p657 ∨ p224)
    (h26879 : p581 ∨ p576)
    (h22768 : (¬ p864) ∨ (¬ p17) ∨ (¬ p8) ∨ (¬ p581) ∨ (¬ p83) ∨ (¬ p657) ∨ (¬ p1249)) : (¬ p864) ∨ (¬ p1249) ∨ (¬ p8) ∨ p224 ∨ (¬ p83) ∨ (¬ p17) ∨ p576 := by
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
  have u2 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h22768 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step31414 (p8 p158 p224 p576 p657 p918 p928 : Prop)
    (h26901 : p928 ∨ p918)
    (h26887 : p657 ∨ p224)
    (h16254 : (¬ p8) ∨ (¬ p158) ∨ (¬ p576) ∨ (¬ p657) ∨ (¬ p928)) : p918 ∨ (¬ p8) ∨ (¬ p576) ∨ (¬ p158) ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p918) := fun hu => hn (Or.inl hu)
  have u1 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16254 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step31415 (p8 p310 p344 p346 p961 p1080 : Prop)
    (h26863 : p346 ∨ p344)
    (h16296 : (¬ p8) ∨ (¬ p310) ∨ (¬ p346) ∨ (¬ p961) ∨ (¬ p1080)) : (¬ p961) ∨ (¬ p8) ∨ (¬ p310) ∨ (¬ p1080) ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p961 := by
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
  have u3 : p1080 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16296 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u3)

theorem step31416 (p8 p41 p45 p63 p85 p101 p102 p224 p306 p422 p657 p1004 : Prop)
    (h26887 : p657 ∨ p224)
    (h26837 : p102 ∨ p101)
    (h26831 : p45 ∨ p41)
    (h26835 : p85 ∨ p63)
    (h19960 : (¬ p8) ∨ (¬ p45) ∨ (¬ p85) ∨ (¬ p102) ∨ (¬ p306) ∨ (¬ p422) ∨ (¬ p657) ∨ (¬ p1004)) : (¬ p422) ∨ (¬ p306) ∨ p224 ∨ p101 ∨ (¬ p1004) ∨ p41 ∨ (¬ p8) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u11 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h19960 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u4)

theorem step31417 (p8 p63 p85 p106 p225 p258 p576 : Prop)
    (h26835 : p85 ∨ p63)
    (h22769 : (¬ p8) ∨ (¬ p225) ∨ (¬ p85) ∨ (¬ p106) ∨ (¬ p258) ∨ (¬ p576)) : (¬ p258) ∨ p63 ∨ (¬ p106) ∨ (¬ p576) ∨ (¬ p225) ∨ (¬ p8) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p63) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h22769 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u3)

theorem step31418 (p8 p90 p242 p836 p918 : Prop)
    (h26586 : p90)
    (h17206 : (¬ p8) ∨ (¬ p90) ∨ (¬ p242) ∨ (¬ p836) ∨ (¬ p918)) : (¬ p8) ∨ (¬ p836) ∨ (¬ p918) ∨ (¬ p242) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
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
  have u3 : p242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p90 := by
    exact h26586
  rcases h17206 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)

theorem step31419 (p8 p101 p102 p306 p836 p1115 p1116 : Prop)
    (h26837 : p102 ∨ p101)
    (h26915 : p1116 ∨ p1115)
    (h18521 : (¬ p8) ∨ (¬ p102) ∨ (¬ p306) ∨ (¬ p836) ∨ (¬ p1116)) : (¬ p8) ∨ (¬ p306) ∨ p101 ∨ p1115 ∨ (¬ p836) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18521 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u6)

theorem step31420 (p8 p106 p224 p306 p419 p539 p657 : Prop)
    (h26887 : p657 ∨ p224)
    (h16197 : (¬ p8) ∨ (¬ p106) ∨ (¬ p306) ∨ (¬ p419) ∨ (¬ p539) ∨ (¬ p657)) : (¬ p306) ∨ p224 ∨ (¬ p8) ∨ (¬ p106) ∨ (¬ p539) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p539 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16197 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)

theorem step31421 (p8 p108 p121 p344 p346 p557 p1080 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26863 : p346 ∨ p344)
    (h16334 : (¬ p8) ∨ (¬ p108) ∨ (¬ p346) ∨ (¬ p557) ∨ (¬ p1080) ∨ (¬ p1206)) : p121 ∨ (¬ p557) ∨ (¬ p1080) ∨ p344 ∨ (¬ p108) ∨ (¬ p8) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1080 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16334 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)

theorem step31423 (p4 p8 p10 p101 p102 p312 : Prop)
    (h26837 : p102 ∨ p101)
    (h19628 : (¬ p4) ∨ (¬ p8) ∨ (¬ p10) ∨ (¬ p102) ∨ (¬ p312)) : (¬ p312) ∨ (¬ p10) ∨ (¬ p4) ∨ (¬ p8) ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p312 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19628 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)

theorem step31424 (p8 p224 p419 p539 p563 p657 : Prop)
    (h26887 : p657 ∨ p224)
    (h16237 : (¬ p8) ∨ (¬ p419) ∨ (¬ p539) ∨ (¬ p563) ∨ (¬ p657)) : p224 ∨ (¬ p539) ∨ (¬ p419) ∨ (¬ p8) ∨ (¬ p563) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p224) := fun hu => hn (Or.inl hu)
  have u1 : p539 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p563 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h16237 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)

theorem step31426 (p8 p101 p121 p194 p206 p242 p836 p961 p1115 p1116 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h19736 : (¬ p8) ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p194) ∨ (¬ p206) ∨ (¬ p242) ∨ (¬ p836) ∨ (¬ p961) ∨ (¬ p1116)) : (¬ p836) ∨ (¬ p101) ∨ (¬ p961) ∨ (¬ p8) ∨ (¬ p121) ∨ (¬ p194) ∨ p1115 ∨ (¬ p242) ∨ (¬ p206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19736 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u2)
  · exact False.elim (q8 u9)

theorem step31427 (p8 p134 p142 p207 p310 p344 p346 p1076 p1077 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26841 : p142 ∨ p134)
    (h26863 : p346 ∨ p344)
    (h19500 : (¬ p8) ∨ (¬ p142) ∨ (¬ p207) ∨ (¬ p310) ∨ (¬ p346) ∨ (¬ p1077)) : p1076 ∨ (¬ p310) ∨ (¬ p8) ∨ p134 ∨ p344 ∨ (¬ p207) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1076) := fun hu => hn (Or.inl hu)
  have u1 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19500 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u6)

theorem step31428 (p8 p224 p303 p312 p345 p657 : Prop)
    (h26887 : p657 ∨ p224)
    (h17757 : (¬ p8) ∨ (¬ p303) ∨ (¬ p312) ∨ (¬ p345) ∨ (¬ p657)) : (¬ p312) ∨ (¬ p8) ∨ p224 ∨ (¬ p303) ∨ (¬ p345) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p312 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p345 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17757 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)

theorem step31429 (p8 p163 p167 p195 p211 p225 p310 : Prop)
    (h26843 : p167 ∨ p163)
    (h18583 : (¬ p8) ∨ (¬ p167) ∨ (¬ p195) ∨ (¬ p211) ∨ (¬ p225) ∨ (¬ p310)) : (¬ p8) ∨ p163 ∨ (¬ p310) ∨ (¬ p195) ∨ (¬ p225) ∨ (¬ p211) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18583 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u2)

theorem step31432 (p8 p163 p167 p195 p225 p561 : Prop)
    (h26843 : p167 ∨ p163)
    (h18106 : (¬ p8) ∨ (¬ p167) ∨ (¬ p195) ∨ (¬ p225) ∨ (¬ p561)) : (¬ p8) ∨ p163 ∨ (¬ p561) ∨ (¬ p195) ∨ (¬ p225) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18106 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u2)

theorem step31434 (p8 p224 p244 p657 p789 p834 p858 : Prop)
    (h26887 : p657 ∨ p224)
    (h26897 : p858 ∨ p789)
    (h16516 : (¬ p8) ∨ (¬ p244) ∨ (¬ p657) ∨ (¬ p834) ∨ (¬ p858)) : p224 ∨ (¬ p8) ∨ (¬ p244) ∨ (¬ p834) ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p224) := fun hu => hn (Or.inl hu)
  have u1 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p244 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p834 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16516 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)

theorem step31435 (p8 p224 p534 p657 p769 : Prop)
    (h26887 : p657 ∨ p224)
    (h17471 : (¬ p8) ∨ (¬ p534) ∨ (¬ p657) ∨ (¬ p769)) : (¬ p769) ∨ (¬ p534) ∨ p224 ∨ (¬ p8) := by
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
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17471 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step31436 (p8 p14 p224 p557 p657 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26887 : p657 ∨ p224)
    (h17300 : (¬ p8) ∨ (¬ p14) ∨ (¬ p557) ∨ (¬ p657) ∨ (¬ p1333)) : (¬ p557) ∨ p1325 ∨ p224 ∨ (¬ p8) ∨ (¬ p14) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17300 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step31438 (p8 p258 p268 p310 p344 p346 : Prop)
    (h26863 : p346 ∨ p344)
    (h16441 : (¬ p8) ∨ (¬ p258) ∨ (¬ p268) ∨ (¬ p310) ∨ (¬ p346)) : (¬ p258) ∨ p344 ∨ (¬ p8) ∨ (¬ p310) ∨ (¬ p268) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p310 := by
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
  rcases h16441 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)

theorem step31441 (p8 p14 p72 p225 p229 p561 : Prop)
    (h26849 : p229 ∨ p14)
    (h19206 : (¬ p8) ∨ (¬ p72) ∨ (¬ p225) ∨ (¬ p229) ∨ (¬ p561)) : p14 ∨ (¬ p561) ∨ (¬ p72) ∨ (¬ p8) ∨ (¬ p225) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19206 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)

theorem step31443 (p8 p158 p189 p193 p728 p918 p928 p1330 p1349 p1489 : Prop)
    (h26901 : p928 ∨ p918)
    (h26845 : p193 ∨ p189)
    (h18456 : (¬ p8) ∨ (¬ p158) ∨ (¬ p193) ∨ (¬ p728) ∨ (¬ p928) ∨ (¬ p1330) ∨ (¬ p1349) ∨ (¬ p1489)) : (¬ p728) ∨ (¬ p8) ∨ (¬ p1330) ∨ (¬ p1349) ∨ (¬ p158) ∨ (¬ p1489) ∨ p918 ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h18456 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u5)

theorem step31445 (p8 p106 p225 p1055 p1076 p1077 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h19300 : (¬ p8) ∨ (¬ p106) ∨ (¬ p225) ∨ (¬ p1055) ∨ (¬ p1077)) : (¬ p1055) ∨ p1076 ∨ (¬ p106) ∨ (¬ p225) ∨ (¬ p8) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19300 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)

theorem step31446 (p8 p101 p143 p262 p310 p344 p346 : Prop)
    (h26863 : p346 ∨ p344)
    (h16294 : (¬ p8) ∨ (¬ p101) ∨ (¬ p143) ∨ (¬ p262) ∨ (¬ p310) ∨ (¬ p346)) : (¬ p101) ∨ p344 ∨ (¬ p262) ∨ (¬ p8) ∨ (¬ p310) ∨ (¬ p143) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p143 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16294 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)

theorem step31450 (p3 p5 p226 p595 p940 p985 p1286 p1325 p1333 : Prop)
    (h26847 : p226 ∨ p3)
    (h26931 : p1333 ∨ p1325)
    (h20595 : (¬ p5) ∨ (¬ p226) ∨ (¬ p595) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1286) ∨ (¬ p1333)) : (¬ p940) ∨ p3 ∨ (¬ p1286) ∨ (¬ p5) ∨ p1325 ∨ (¬ p595) ∨ (¬ p985) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p595 := by
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
    · exact False.elim (u1 q1)
  have u8 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20595 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u8)

theorem step31451 (p3 p5 p225 p226 p303 p347 p595 p1286 : Prop)
    (h26847 : p226 ∨ p3)
    (h18244 : (¬ p5) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p303) ∨ (¬ p347) ∨ (¬ p595) ∨ (¬ p1286)) : (¬ p1286) ∨ (¬ p595) ∨ (¬ p347) ∨ (¬ p225) ∨ (¬ p5) ∨ (¬ p303) ∨ p3 := by
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
  have u2 : p347 := by
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
  have u5 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18244 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u0)

theorem step31452 (p5 p101 p102 p121 p124 p206 p304 p389 p595 p1206 p1286 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26859 : p304 ∨ p124)
    (h26837 : p102 ∨ p101)
    (h20610 : (¬ p5) ∨ (¬ p102) ∨ (¬ p206) ∨ (¬ p304) ∨ (¬ p389) ∨ (¬ p595) ∨ (¬ p1206) ∨ (¬ p1286)) : p121 ∨ (¬ p389) ∨ p124 ∨ (¬ p5) ∨ (¬ p206) ∨ p101 ∨ (¬ p1286) ∨ (¬ p595) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20610 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u6)

theorem step31453 (p5 p107 p124 p161 p206 p225 p304 p734 p1225 p1229 p1335 : Prop)
    (h26925 : p1225 ∨ p161)
    (h26859 : p304 ∨ p124)
    (h18425 : (¬ p5) ∨ (¬ p107) ∨ (¬ p206) ∨ (¬ p225) ∨ (¬ p304) ∨ (¬ p734) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1335)) : p161 ∨ p124 ∨ (¬ p5) ∨ (¬ p1229) ∨ (¬ p225) ∨ (¬ p206) ∨ (¬ p1335) ∨ (¬ p734) ∨ (¬ p107) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p161) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p107 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18425 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u3)
  · exact False.elim (q8 u6)

theorem step31454 (p2 p5 p303 p387 p420 p431 p435 p495 p499 p601 : Prop)
    (h26875 : p499 ∨ p495)
    (h26881 : p601 ∨ p420)
    (h26867 : p387 ∨ p303)
    (h19408 : (¬ p2) ∨ (¬ p5) ∨ (¬ p387) ∨ (¬ p431) ∨ (¬ p435) ∨ (¬ p499) ∨ (¬ p601)) : (¬ p2) ∨ (¬ p431) ∨ (¬ p435) ∨ p495 ∨ p420 ∨ (¬ p5) ∨ p303 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19408 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u8)

theorem step31455 (p5 p10 p63 p206 p517 p1385 p1393 p1624 p1665 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h18950 : (¬ p5) ∨ (¬ p10) ∨ (¬ p63) ∨ (¬ p206) ∨ (¬ p517) ∨ (¬ p1393) ∨ (¬ p1624) ∨ (¬ p1665)) : (¬ p1624) ∨ (¬ p63) ∨ (¬ p1665) ∨ (¬ p206) ∨ (¬ p10) ∨ (¬ p517) ∨ (¬ p5) ∨ p1385 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1624 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1665 := by
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
  have u6 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h18950 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u2)

theorem step31456 (p5 p10 p63 p101 p102 p124 p206 p304 p517 p1385 p1393 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h26859 : p304 ∨ p124)
    (h26837 : p102 ∨ p101)
    (h19011 : (¬ p5) ∨ (¬ p10) ∨ (¬ p63) ∨ (¬ p102) ∨ (¬ p206) ∨ (¬ p304) ∨ (¬ p517) ∨ (¬ p1393)) : (¬ p517) ∨ (¬ p10) ∨ (¬ p206) ∨ p1385 ∨ p124 ∨ p101 ∨ (¬ p63) ∨ (¬ p5) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p517 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19011 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u8)

theorem step31457 (p2 p5 p89 p185 p237 p419 p918 p1325 p1385 p1393 : Prop)
    (h26851 : p237 ∨ p185)
    (h26933 : p1393 ∨ p1385)
    (h18496 : (¬ p2) ∨ (¬ p5) ∨ (¬ p89) ∨ (¬ p237) ∨ (¬ p419) ∨ (¬ p918) ∨ (¬ p1325) ∨ (¬ p1393)) : (¬ p2) ∨ p185 ∨ (¬ p918) ∨ (¬ p89) ∨ p1385 ∨ (¬ p1325) ∨ (¬ p5) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18496 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u9)

theorem step31458 (p2 p5 p89 p185 p237 p419 p860 p918 p1273 : Prop)
    (h26851 : p237 ∨ p185)
    (h18361 : (¬ p2) ∨ (¬ p5) ∨ (¬ p89) ∨ (¬ p237) ∨ (¬ p419) ∨ (¬ p860) ∨ (¬ p918) ∨ (¬ p1273)) : (¬ p918) ∨ (¬ p1273) ∨ (¬ p860) ∨ (¬ p2) ∨ (¬ p5) ∨ (¬ p419) ∨ (¬ p89) ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p860 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h18361 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u1)

theorem step31461 (p2 p5 p89 p185 p237 p435 p980 p983 p1115 p1116 p1335 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h26903 : p983 ∨ p980)
    (h26851 : p237 ∨ p185)
    (h18342 : (¬ p2) ∨ (¬ p5) ∨ (¬ p89) ∨ (¬ p237) ∨ (¬ p435) ∨ (¬ p983) ∨ (¬ p1116) ∨ (¬ p1335)) : (¬ p2) ∨ (¬ p89) ∨ p1115 ∨ p980 ∨ (¬ p5) ∨ p185 ∨ (¬ p435) ∨ (¬ p1335) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18342 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u7)

theorem step31465 (p17 p576 p581 p918 p1115 : Prop)
    (h26879 : p581 ∨ p576)
    (h19347 : (¬ p17) ∨ (¬ p581) ∨ (¬ p918) ∨ (¬ p1115)) : (¬ p918) ∨ (¬ p1115) ∨ (¬ p17) ∨ p576 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19347 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)

theorem step31466 (p17 p576 p581 p789 p790 : Prop)
    (h26879 : p581 ∨ p576)
    (h19494 : (¬ p17) ∨ (¬ p581) ∨ (¬ p789) ∨ (¬ p790)) : (¬ p790) ∨ (¬ p789) ∨ p576 ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19494 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)

theorem step31467 (p434 p576 p581 p1015 p1385 : Prop)
    (h26879 : p581 ∨ p576)
    (h20403 : (¬ p434) ∨ (¬ p581) ∨ (¬ p1015) ∨ (¬ p1385)) : (¬ p434) ∨ (¬ p1015) ∨ p576 ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20403 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)

theorem step31468 (p63 p258 p288 p576 p581 p1076 p1077 : Prop)
    (h26879 : p581 ∨ p576)
    (h26911 : p1077 ∨ p1076)
    (h26855 : p288 ∨ p258)
    (h17258 : (¬ p63) ∨ (¬ p288) ∨ (¬ p581) ∨ (¬ p1077)) : p576 ∨ p1076 ∨ (¬ p63) ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p576) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17258 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step31469 (p63 p382 p576 p581 p713 p897 p1325 p1449 p1651 : Prop)
    (h26879 : p581 ∨ p576)
    (h18586 : (¬ p63) ∨ (¬ p382) ∨ (¬ p581) ∨ (¬ p713) ∨ (¬ p897) ∨ (¬ p1325) ∨ (¬ p1449) ∨ (¬ p1651)) : (¬ p1651) ∨ (¬ p897) ∨ (¬ p1325) ∨ (¬ p713) ∨ p576 ∨ (¬ p1449) ∨ (¬ p63) ∨ (¬ p382) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1651 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p713 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1449 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p63 := by
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
    · exact False.elim (u4 q1)
  rcases h18586 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u0)

theorem step31470 (p17 p41 p45 p424 p576 p581 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h26831 : p45 ∨ p41)
    (h26879 : p581 ∨ p576)
    (h17681 : (¬ p17) ∨ (¬ p45) ∨ (¬ p581) ∨ (¬ p796)) : p424 ∨ p41 ∨ (¬ p17) ∨ p576 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p41) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17681 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)

theorem step31471 (p17 p41 p45 p576 p581 p790 : Prop)
    (h26879 : p581 ∨ p576)
    (h26831 : p45 ∨ p41)
    (h20219 : (¬ p17) ∨ (¬ p45) ∨ (¬ p581) ∨ (¬ p790)) : p576 ∨ p41 ∨ (¬ p790) ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p576) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p41) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
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
  rcases h20219 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)

theorem step31472 (p161 p258 p288 p576 p581 p665 p1076 p1077 p1274 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26911 : p1077 ∨ p1076)
    (h26855 : p288 ∨ p258)
    (h26879 : p581 ∨ p576)
    (h17436 : (¬ p161) ∨ (¬ p288) ∨ (¬ p581) ∨ (¬ p665) ∨ (¬ p1077) ∨ (¬ p1274) ∨ (¬ p1333)) : (¬ p161) ∨ p1325 ∨ (¬ p1274) ∨ p1076 ∨ p258 ∨ (¬ p665) ∨ p576 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1274 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h17436 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u7)

theorem step31474 (p185 p237 p382 p576 p581 p728 p819 p836 p840 p1385 : Prop)
    (h26879 : p581 ∨ p576)
    (h26895 : p840 ∨ p836)
    (h26851 : p237 ∨ p185)
    (h26124 : (¬ p581) ∨ (¬ p237) ∨ (¬ p819) ∨ (¬ p728) ∨ (¬ p1385) ∨ (¬ p382) ∨ (¬ p840)) : (¬ p1385) ∨ p576 ∨ (¬ p382) ∨ p836 ∨ (¬ p819) ∨ (¬ p728) ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p819 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h26124 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u8)

theorem step31479 (p189 p258 p288 p576 p581 p790 p1385 : Prop)
    (h26855 : p288 ∨ p258)
    (h26879 : p581 ∨ p576)
    (h18641 : (¬ p189) ∨ (¬ p288) ∨ (¬ p581) ∨ (¬ p790) ∨ (¬ p1385)) : (¬ p1385) ∨ (¬ p790) ∨ p258 ∨ (¬ p189) ∨ p576 := by
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
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18641 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)

theorem step31481 (p10 p17 p518 p576 p581 p790 : Prop)
    (h26879 : p581 ∨ p576)
    (h16279 : (¬ p10) ∨ (¬ p17) ∨ (¬ p518) ∨ (¬ p581) ∨ (¬ p790)) : (¬ p10) ∨ p576 ∨ (¬ p790) ∨ (¬ p17) ∨ (¬ p518) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p518 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16279 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)

theorem step31482 (p17 p88 p576 p581 : Prop)
    (h26879 : p581 ∨ p576)
    (h8740 : (¬ p17) ∨ (¬ p88) ∨ (¬ p581)) : p576 ∨ (¬ p17) ∨ (¬ p88) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p576) := fun hu => hn (Or.inl hu)
  have u1 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8740 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)

theorem step31483 (p17 p83 p576 p581 p929 p1096 : Prop)
    (h26879 : p581 ∨ p576)
    (h16620 : (¬ p17) ∨ (¬ p83) ∨ (¬ p581) ∨ (¬ p929) ∨ (¬ p1096)) : p576 ∨ (¬ p1096) ∨ (¬ p83) ∨ (¬ p17) ∨ (¬ p929) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p576) := fun hu => hn (Or.inl hu)
  have u1 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h16620 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u1)

theorem step31484 (p17 p83 p576 p581 p1249 p1489 : Prop)
    (h26879 : p581 ∨ p576)
    (h17676 : (¬ p17) ∨ (¬ p83) ∨ (¬ p581) ∨ (¬ p1249) ∨ (¬ p1489)) : (¬ p1249) ∨ p576 ∨ (¬ p17) ∨ (¬ p1489) ∨ (¬ p83) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17676 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u3)

theorem step31485 (p17 p83 p576 p581 p789 p858 p1385 : Prop)
    (h26879 : p581 ∨ p576)
    (h26897 : p858 ∨ p789)
    (h19275 : (¬ p17) ∨ (¬ p83) ∨ (¬ p581) ∨ (¬ p858) ∨ (¬ p1385)) : (¬ p1385) ∨ p576 ∨ p789 ∨ (¬ p83) ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19275 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u0)

theorem step31486 (p17 p83 p576 p581 p1015 p1385 : Prop)
    (h26879 : p581 ∨ p576)
    (h20069 : (¬ p17) ∨ (¬ p83) ∨ (¬ p581) ∨ (¬ p1015) ∨ (¬ p1385)) : (¬ p1385) ∨ p576 ∨ (¬ p83) ∨ (¬ p17) ∨ (¬ p1015) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20069 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u0)

theorem step31487 (p17 p83 p576 p581 p1076 p1077 p1118 p1249 : Prop)
    (h26879 : p581 ∨ p576)
    (h26911 : p1077 ∨ p1076)
    (h20073 : (¬ p17) ∨ (¬ p83) ∨ (¬ p581) ∨ (¬ p1077) ∨ (¬ p1118) ∨ (¬ p1249)) : (¬ p1249) ∨ p576 ∨ (¬ p83) ∨ (¬ p17) ∨ (¬ p1118) ∨ p1076 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1118 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20073 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u0)

theorem step31491 (p41 p45 p189 p193 p258 p288 p576 p581 : Prop)
    (h26845 : p193 ∨ p189)
    (h26879 : p581 ∨ p576)
    (h26855 : p288 ∨ p258)
    (h26831 : p45 ∨ p41)
    (h17430 : (¬ p45) ∨ (¬ p193) ∨ (¬ p288) ∨ (¬ p581)) : p189 ∨ p576 ∨ p258 ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p189) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17430 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)

theorem step31492 (p125 p262 p303 p362 p387 p576 p581 p1325 p1333 : Prop)
    (h26867 : p387 ∨ p303)
    (h26931 : p1333 ∨ p1325)
    (h26879 : p581 ∨ p576)
    (h26865 : p362 ∨ p125)
    (h17522 : (¬ p262) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p581) ∨ (¬ p1333)) : p303 ∨ p1325 ∨ p576 ∨ p125 ∨ (¬ p262) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17522 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u6)

theorem step31493 (p125 p224 p262 p303 p362 p387 p576 p581 : Prop)
    (h26867 : p387 ∨ p303)
    (h26879 : p581 ∨ p576)
    (h26865 : p362 ∨ p125)
    (h16278 : (¬ p224) ∨ (¬ p262) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p581)) : p303 ∨ (¬ p224) ∨ (¬ p262) ∨ p576 ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16278 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)

theorem step31494 (p10 p101 p124 p262 p323 p576 p581 : Prop)
    (h26879 : p581 ∨ p576)
    (h26861 : p323 ∨ p10)
    (h16277 : (¬ p101) ∨ (¬ p124) ∨ (¬ p262) ∨ (¬ p323) ∨ (¬ p581)) : (¬ p101) ∨ (¬ p124) ∨ p576 ∨ p10 ∨ (¬ p262) := by
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
  have u2 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16277 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step31495 (p258 p288 p515 p576 p581 p1385 : Prop)
    (h26855 : p288 ∨ p258)
    (h26879 : p581 ∨ p576)
    (h24197 : (¬ p515) ∨ (¬ p1385) ∨ (¬ p288) ∨ (¬ p581)) : (¬ p515) ∨ (¬ p1385) ∨ p258 ∨ p576 := by
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
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h24197 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step31497 (p10 p101 p102 p126 p576 p581 : Prop)
    (h26837 : p102 ∨ p101)
    (h26879 : p581 ∨ p576)
    (h17133 : (¬ p10) ∨ (¬ p102) ∨ (¬ p126) ∨ (¬ p581)) : (¬ p10) ∨ (¬ p126) ∨ p101 ∨ p576 := by
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
  have u3 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17133 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)

theorem step31498 (p63 p126 p434 p576 p581 : Prop)
    (h26879 : p581 ∨ p576)
    (h17418 : (¬ p63) ∨ (¬ p126) ∨ (¬ p434) ∨ (¬ p581)) : (¬ p434) ∨ p576 ∨ (¬ p63) ∨ (¬ p126) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17418 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)

theorem step31499 (p63 p126 p303 p387 p576 p581 : Prop)
    (h26879 : p581 ∨ p576)
    (h26867 : p387 ∨ p303)
    (h19398 : (¬ p63) ∨ (¬ p126) ∨ (¬ p387) ∨ (¬ p581)) : p576 ∨ p303 ∨ (¬ p63) ∨ (¬ p126) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p576) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19398 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step31500 (p11 p63 p576 p581 p1443 p1452 : Prop)
    (h26879 : p581 ∨ p576)
    (h26935 : p1443 ∨ p11)
    (h17969 : (¬ p63) ∨ (¬ p581) ∨ (¬ p1443) ∨ (¬ p1452)) : (¬ p1452) ∨ p576 ∨ p11 ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17969 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)

theorem step31501 (p63 p576 p581 p980 p1055 p1103 p1449 p1651 : Prop)
    (h26879 : p581 ∨ p576)
    (h17818 : (¬ p63) ∨ (¬ p581) ∨ (¬ p980) ∨ (¬ p1055) ∨ (¬ p1103) ∨ (¬ p1449) ∨ (¬ p1651)) : (¬ p1651) ∨ p576 ∨ (¬ p1055) ∨ (¬ p63) ∨ (¬ p1449) ∨ (¬ p1103) ∨ (¬ p980) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1651 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1449 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17818 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u0)

theorem step31503 (p8 p11 p63 p224 p228 p576 p581 p710 p1103 p1443 : Prop)
    (h26879 : p581 ∨ p576)
    (h26889 : p710 ∨ p8)
    (h26935 : p1443 ∨ p11)
    (h17970 : (¬ p63) ∨ (¬ p224) ∨ (¬ p228) ∨ (¬ p581) ∨ (¬ p710) ∨ (¬ p1103) ∨ (¬ p1443)) : (¬ p1103) ∨ p576 ∨ (¬ p228) ∨ (¬ p224) ∨ p8 ∨ p11 ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17970 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u9)

theorem step31504 (p11 p63 p422 p576 p581 p980 p983 p1081 p1145 p1226 p1235 p1443 : Prop)
    (h26903 : p983 ∨ p980)
    (h26879 : p581 ∨ p576)
    (h26935 : p1443 ∨ p11)
    (h19401 : (¬ p63) ∨ (¬ p422) ∨ (¬ p581) ∨ (¬ p983) ∨ (¬ p1081) ∨ (¬ p1145) ∨ (¬ p1226) ∨ (¬ p1235) ∨ (¬ p1443)) : (¬ p422) ∨ p980 ∨ (¬ p1235) ∨ (¬ p63) ∨ (¬ p1145) ∨ p576 ∨ (¬ p1226) ∨ p11 ∨ (¬ p1081) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1235 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1145 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u11 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h19401 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u2)
  · exact False.elim (q8 u11)

theorem step31505 (p87 p101 p134 p189 p227 p262 p576 p581 p1084 : Prop)
    (h26879 : p581 ∨ p576)
    (h18457 : (¬ p87) ∨ (¬ p101) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p227) ∨ (¬ p262) ∨ (¬ p581) ∨ (¬ p1084)) : (¬ p101) ∨ (¬ p227) ∨ (¬ p134) ∨ (¬ p1084) ∨ (¬ p262) ∨ (¬ p189) ∨ p576 ∨ (¬ p87) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18457 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u3)

theorem step31506 (p185 p237 p576 p581 p980 p983 p1015 p1115 p1116 p1335 p1385 : Prop)
    (h26903 : p983 ∨ p980)
    (h26879 : p581 ∨ p576)
    (h26915 : p1116 ∨ p1115)
    (h26851 : p237 ∨ p185)
    (h19219 : (¬ p237) ∨ (¬ p581) ∨ (¬ p983) ∨ (¬ p1015) ∨ (¬ p1116) ∨ (¬ p1335) ∨ (¬ p1385)) : p980 ∨ (¬ p1385) ∨ p576 ∨ (¬ p1015) ∨ (¬ p1335) ∨ p1115 ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19219 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u1)

theorem step31507 (p5 p6 p101 p344 p346 p382 p406 p576 p581 p620 p1287 p1387 : Prop)
    (h26869 : p406 ∨ p382)
    (h26879 : p581 ∨ p576)
    (h26863 : p346 ∨ p344)
    (h20640 : (¬ p5) ∨ (¬ p6) ∨ (¬ p101) ∨ (¬ p346) ∨ (¬ p406) ∨ (¬ p581) ∨ (¬ p620) ∨ (¬ p1287) ∨ (¬ p1387)) : p382 ∨ p576 ∨ p344 ∨ (¬ p6) ∨ (¬ p1387) ∨ (¬ p101) ∨ (¬ p620) ∨ (¬ p5) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p620 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u11 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20640 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u4)

theorem step31533 (p125 p126 p265 p362 : Prop)
    (h26864 : (¬ p125) ∨ (¬ p362))
    (h11184 : (¬ p126) ∨ (¬ p265) ∨ p362) : (¬ p125) ∨ (¬ p265) ∨ (¬ p126) := by
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
  have u2 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p362) := by
    rcases h26864 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h11184 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (u3 q2)

theorem step31534 (p258 p285 p288 : Prop)
    (h26855 : p288 ∨ p258)
    (h18902 : p285 ∨ (¬ p288)) : p285 ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p285) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p258) := fun hu => hn (Or.inr hu)
  have u2 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18902 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)

theorem step31535 (p17 p256 p258 p288 p344 p836 : Prop)
    (h26853 : p256 ∨ p17)
    (h26855 : p288 ∨ p258)
    (h16582 : (¬ p256) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p836)) : (¬ p836) ∨ (¬ p344) ∨ p17 ∨ p258 := by
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
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16582 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)

theorem step31538 (p63 p258 p288 p495 p633 p636 : Prop)
    (h26855 : p288 ∨ p258)
    (h26885 : p636 ∨ p633)
    (h16855 : (¬ p63) ∨ (¬ p288) ∨ (¬ p495) ∨ (¬ p636)) : p258 ∨ p633 ∨ (¬ p63) ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p258) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p633) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16855 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)

theorem step31539 (p63 p258 p288 p344 p576 p581 : Prop)
    (h26879 : p581 ∨ p576)
    (h26855 : p288 ∨ p258)
    (h17217 : (¬ p63) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p581)) : p576 ∨ (¬ p344) ∨ (¬ p63) ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p576) := fun hu => hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17217 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)

theorem step31540 (p126 p258 p288 p301 p438 p687 : Prop)
    (h26857 : p301 ∨ p126)
    (h26855 : p288 ∨ p258)
    (h17227 : (¬ p288) ∨ (¬ p301) ∨ (¬ p438) ∨ (¬ p687)) : p126 ∨ (¬ p438) ∨ p258 ∨ (¬ p687) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17227 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)

theorem step31541 (p17 p256 p258 p288 p344 p382 p821 p906 p1286 : Prop)
    (h26855 : p288 ∨ p258)
    (h26853 : p256 ∨ p17)
    (h17445 : (¬ p256) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p382) ∨ (¬ p821) ∨ (¬ p906) ∨ (¬ p1286)) : (¬ p906) ∨ p258 ∨ p17 ∨ (¬ p1286) ∨ (¬ p382) ∨ (¬ p344) ∨ (¬ p821) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p906 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p258) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p821 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17445 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u3)

theorem step31542 (p63 p126 p258 p288 p301 p420 p601 : Prop)
    (h26857 : p301 ∨ p126)
    (h26855 : p288 ∨ p258)
    (h26881 : p601 ∨ p420)
    (h26465 : (¬ p301) ∨ (¬ p288) ∨ (¬ p601) ∨ (¬ p63)) : p126 ∨ (¬ p63) ∨ p258 ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h26465 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)

theorem step31543 (p17 p256 p258 p288 p790 p814 p1385 p1393 : Prop)
    (h26893 : p814 ∨ p790)
    (h26933 : p1393 ∨ p1385)
    (h26853 : p256 ∨ p17)
    (h26855 : p288 ∨ p258)
    (h18021 : (¬ p256) ∨ (¬ p288) ∨ (¬ p814) ∨ (¬ p1393)) : p790 ∨ p1385 ∨ p17 ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p790) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1385) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18021 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step31544 (p17 p256 p258 p288 p789 p790 p814 p858 : Prop)
    (h26893 : p814 ∨ p790)
    (h26853 : p256 ∨ p17)
    (h26897 : p858 ∨ p789)
    (h26855 : p288 ∨ p258)
    (h18096 : (¬ p256) ∨ (¬ p288) ∨ (¬ p814) ∨ (¬ p858)) : p790 ∨ p17 ∨ p789 ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p790) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
    · exact False.elim (u2 q1)
  have u7 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18096 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)

theorem step31545 (p11 p15 p124 p258 p288 p304 p423 p1210 : Prop)
    (h26859 : p304 ∨ p124)
    (h26855 : p288 ∨ p258)
    (h26125 : (¬ p1210) ∨ (¬ p11) ∨ (¬ p288) ∨ (¬ p15) ∨ (¬ p304) ∨ (¬ p423)) : p124 ∨ p258 ∨ (¬ p423) ∨ (¬ p15) ∨ (¬ p1210) ∨ (¬ p11) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p258) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h26125 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)

theorem step31547 (p125 p258 p265 p288 p438 p728 : Prop)
    (h26855 : p288 ∨ p258)
    (h18033 : (¬ p125) ∨ (¬ p265) ∨ (¬ p288) ∨ (¬ p438) ∨ (¬ p728)) : (¬ p125) ∨ (¬ p728) ∨ (¬ p438) ∨ p258 ∨ (¬ p265) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18033 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u1)

theorem step31548 (p6 p10 p126 p127 p186 p258 p288 p301 p323 : Prop)
    (h26857 : p301 ∨ p126)
    (h26839 : p127 ∨ p6)
    (h26855 : p288 ∨ p258)
    (h26861 : p323 ∨ p10)
    (h16752 : (¬ p127) ∨ (¬ p186) ∨ (¬ p288) ∨ (¬ p301) ∨ (¬ p323)) : p126 ∨ p6 ∨ p258 ∨ (¬ p186) ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16752 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u8)

theorem step31550 (p17 p194 p256 p258 p288 p344 p382 p419 p477 p545 p996 : Prop)
    (h26853 : p256 ∨ p17)
    (h26905 : p996 ∨ p419)
    (h26855 : p288 ∨ p258)
    (h18101 : (¬ p194) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p382) ∨ (¬ p477) ∨ (¬ p545) ∨ (¬ p996)) : (¬ p477) ∨ (¬ p194) ∨ p17 ∨ (¬ p545) ∨ (¬ p344) ∨ p419 ∨ (¬ p382) ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p477 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h18101 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u9)

theorem step31551 (p17 p86 p256 p258 p288 p344 p664 p1074 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26855 : p288 ∨ p258)
    (h26853 : p256 ∨ p17)
    (h18219 : (¬ p86) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p664) ∨ (¬ p1074) ∨ (¬ p1099)) : (¬ p344) ∨ p1096 ∨ p258 ∨ (¬ p1074) ∨ (¬ p664) ∨ (¬ p86) ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18219 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step31555 (p17 p41 p189 p256 p258 p288 : Prop)
    (h26853 : p256 ∨ p17)
    (h26855 : p288 ∨ p258)
    (h16720 : (¬ p41) ∨ (¬ p189) ∨ (¬ p256) ∨ (¬ p288)) : p17 ∨ (¬ p41) ∨ (¬ p189) ∨ p258 := by
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
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16720 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step31560 (p101 p134 p189 p258 p288 : Prop)
    (h26855 : p288 ∨ p258)
    (h16859 : (¬ p101) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p288)) : (¬ p101) ∨ p258 ∨ (¬ p189) ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p258) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16859 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step31561 (p101 p137 p258 p288 : Prop)
    (h26855 : p288 ∨ p258)
    (h12323 : (¬ p101) ∨ (¬ p137) ∨ (¬ p288)) : p258 ∨ (¬ p101) ∨ (¬ p137) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p258) := fun hu => hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p137 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h12323 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)

theorem step31563 (p41 p63 p101 p141 p258 p288 : Prop)
    (h26855 : p288 ∨ p258)
    (h17414 : (¬ p41) ∨ (¬ p63) ∨ (¬ p101) ∨ (¬ p141) ∨ (¬ p288)) : p258 ∨ (¬ p101) ∨ (¬ p141) ∨ (¬ p41) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p258) := fun hu => hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17414 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step31564 (p6 p101 p126 p258 p288 p301 : Prop)
    (h26857 : p301 ∨ p126)
    (h26855 : p288 ∨ p258)
    (h19520 : (¬ p6) ∨ (¬ p101) ∨ (¬ p288) ∨ (¬ p301)) : p126 ∨ (¬ p101) ∨ p258 ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19520 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step31566 (p3 p12 p194 p226 p258 p266 p288 p980 p1036 p1631 p1644 : Prop)
    (h26847 : p226 ∨ p3)
    (h26907 : p1036 ∨ p12)
    (h26855 : p288 ∨ p258)
    (h18997 : (¬ p194) ∨ (¬ p226) ∨ (¬ p266) ∨ (¬ p288) ∨ (¬ p980) ∨ (¬ p1036) ∨ (¬ p1631) ∨ (¬ p1644)) : (¬ p1631) ∨ (¬ p1644) ∨ (¬ p266) ∨ (¬ p194) ∨ p3 ∨ p12 ∨ (¬ p980) ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1631 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1644 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h18997 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u1)

theorem step31567 (p17 p86 p256 p258 p288 p668 p897 p1076 p1077 p1096 p1099 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26853 : p256 ∨ p17)
    (h26913 : p1099 ∨ p1096)
    (h26855 : p288 ∨ p258)
    (h17377 : (¬ p86) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p668) ∨ (¬ p897) ∨ (¬ p1077) ∨ (¬ p1099)) : p1076 ∨ p17 ∨ p1096 ∨ p258 ∨ (¬ p86) ∨ (¬ p668) ∨ (¬ p897) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1076) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p86 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17377 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u9)

theorem step31568 (p17 p86 p256 p258 p288 p595 p616 p665 p1076 p1077 p1287 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26855 : p288 ∨ p258)
    (h26853 : p256 ∨ p17)
    (h26883 : p616 ∨ p595)
    (h17444 : (¬ p86) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p616) ∨ (¬ p665) ∨ (¬ p1077) ∨ (¬ p1287)) : p1076 ∨ p258 ∨ p17 ∨ (¬ p1287) ∨ (¬ p665) ∨ p595 ∨ (¬ p86) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1076) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p258) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17444 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step31569 (p103 p143 p225 p258 p288 p344 : Prop)
    (h26855 : p288 ∨ p258)
    (h16856 : (¬ p103) ∨ (¬ p143) ∨ (¬ p225) ∨ (¬ p288) ∨ (¬ p344)) : (¬ p103) ∨ (¬ p344) ∨ (¬ p225) ∨ p258 ∨ (¬ p143) := by
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
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p143 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16856 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)

theorem step31570 (p3 p14 p16 p18 p19 p71 p124 p143 p229 p258 p261 p288 p304 : Prop)
    (h26849 : p229 ∨ p14)
    (h26859 : p304 ∨ p124)
    (h26829 : p19 ∨ p18)
    (h26855 : p288 ∨ p258)
    (h19317 : (¬ p3) ∨ (¬ p16) ∨ (¬ p19) ∨ (¬ p71) ∨ (¬ p143) ∨ (¬ p229) ∨ (¬ p261) ∨ (¬ p288) ∨ (¬ p304)) : p14 ∨ p124 ∨ (¬ p71) ∨ p18 ∨ (¬ p3) ∨ (¬ p261) ∨ (¬ p16) ∨ p258 ∨ (¬ p143) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p143 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u11 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u12 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h19317 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u12)
  · exact False.elim (q8 u10)

theorem step31572 (p8 p17 p41 p45 p90 p110 p192 p225 p256 p258 p288 p544 p556 p710 : Prop)
    (h26877 : p544 ∨ p225)
    (h26853 : p256 ∨ p17)
    (h26889 : p710 ∨ p8)
    (h26586 : p90)
    (h26855 : p288 ∨ p258)
    (h26831 : p45 ∨ p41)
    (h18530 : (¬ p45) ∨ (¬ p90) ∨ (¬ p110) ∨ (¬ p192) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p544) ∨ (¬ p556) ∨ (¬ p710)) : (¬ p556) ∨ (¬ p110) ∨ p225 ∨ p17 ∨ (¬ p192) ∨ p8 ∨ p258 ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p556 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u11 : p90 := by
    exact h26586
  have u12 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u13 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h18530 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u13)
  · exact False.elim (q1 u11)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u12)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u0)
  · exact False.elim (q8 u10)

theorem step31574 (p63 p85 p303 p595 p1286 : Prop)
    (h26835 : p85 ∨ p63)
    (h16539 : (¬ p85) ∨ (¬ p303) ∨ (¬ p595) ∨ (¬ p1286)) : (¬ p1286) ∨ (¬ p595) ∨ (¬ p303) ∨ p63 := by
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
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16539 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)

theorem step31575 (p63 p85 p224 p595 p1286 : Prop)
    (h26835 : p85 ∨ p63)
    (h16564 : (¬ p85) ∨ (¬ p224) ∨ (¬ p595) ∨ (¬ p1286)) : (¬ p1286) ∨ (¬ p595) ∨ (¬ p224) ∨ p63 := by
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
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16564 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)

theorem step31576 (p41 p45 p63 p85 p224 p382 p406 p424 p545 p617 p796 : Prop)
    (h26869 : p406 ∨ p382)
    (h26891 : p796 ∨ p424)
    (h26835 : p85 ∨ p63)
    (h26831 : p45 ∨ p41)
    (h19959 : (¬ p45) ∨ (¬ p85) ∨ (¬ p224) ∨ (¬ p406) ∨ (¬ p545) ∨ (¬ p617) ∨ (¬ p796)) : p382 ∨ p424 ∨ p63 ∨ (¬ p224) ∨ p41 ∨ (¬ p545) ∨ (¬ p617) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p424) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p617 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19959 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u8)

theorem step31578 (p6 p63 p85 p101 p102 p127 p344 p842 p1385 : Prop)
    (h26839 : p127 ∨ p6)
    (h26835 : p85 ∨ p63)
    (h26837 : p102 ∨ p101)
    (h26126 : (¬ p85) ∨ (¬ p842) ∨ (¬ p127) ∨ (¬ p344) ∨ (¬ p1385) ∨ (¬ p102)) : p6 ∨ (¬ p1385) ∨ (¬ p344) ∨ p63 ∨ (¬ p842) ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p6) := fun hu => hn (Or.inl hu)
  have u1 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p842 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26126 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u8)

theorem step31579 (p6 p63 p85 p101 p102 p127 p1076 p1077 p1124 p1249 : Prop)
    (h26839 : p127 ∨ p6)
    (h26835 : p85 ∨ p63)
    (h26837 : p102 ∨ p101)
    (h26911 : p1077 ∨ p1076)
    (h26127 : (¬ p1124) ∨ (¬ p85) ∨ (¬ p127) ∨ (¬ p1077) ∨ (¬ p1249) ∨ (¬ p102)) : (¬ p1249) ∨ p6 ∨ (¬ p1124) ∨ p63 ∨ p101 ∨ p1076 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26127 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u8)

theorem step31580 (p41 p45 p63 p85 p419 p424 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h26835 : p85 ∨ p63)
    (h26831 : p45 ∨ p41)
    (h16615 : (¬ p45) ∨ (¬ p85) ∨ (¬ p419) ∨ (¬ p796)) : p424 ∨ p63 ∨ (¬ p419) ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p63) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16615 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step31581 (p41 p45 p63 p85 p121 p134 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26831 : p45 ∨ p41)
    (h26835 : p85 ∨ p63)
    (h16844 : (¬ p45) ∨ (¬ p85) ∨ (¬ p134) ∨ (¬ p1206)) : p121 ∨ p41 ∨ p63 ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p41) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16844 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step31582 (p41 p45 p63 p85 p125 p134 p303 p362 p387 p496 p1325 p1333 : Prop)
    (h26867 : p387 ∨ p303)
    (h26931 : p1333 ∨ p1325)
    (h26865 : p362 ∨ p125)
    (h26831 : p45 ∨ p41)
    (h26835 : p85 ∨ p63)
    (h19418 : (¬ p45) ∨ (¬ p85) ∨ (¬ p134) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p496) ∨ (¬ p1333)) : p303 ∨ p1325 ∨ (¬ p134) ∨ p125 ∨ p41 ∨ (¬ p496) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19418 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u11)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u8)

theorem step31583 (p41 p45 p63 p85 p101 p134 : Prop)
    (h26831 : p45 ∨ p41)
    (h26835 : p85 ∨ p63)
    (h17078 : (¬ p45) ∨ (¬ p85) ∨ (¬ p101) ∨ (¬ p134)) : (¬ p101) ∨ p41 ∨ (¬ p134) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p41) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17078 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u2)

theorem step31584 (p63 p85 p595 p1286 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26835 : p85 ∨ p63)
    (h16701 : (¬ p85) ∨ (¬ p595) ∨ (¬ p1286) ∨ (¬ p1333)) : (¬ p1286) ∨ p1325 ∨ (¬ p595) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
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
  rcases h16701 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)

theorem step31587 (p41 p45 p63 p85 p86 p189 p193 : Prop)
    (h26845 : p193 ∨ p189)
    (h26831 : p45 ∨ p41)
    (h26835 : p85 ∨ p63)
    (h16324 : (¬ p45) ∨ (¬ p85) ∨ (¬ p86) ∨ (¬ p193)) : p189 ∨ p41 ∨ p63 ∨ (¬ p86) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p189) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p41) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16324 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step31588 (p41 p45 p63 p85 p422 p1465 : Prop)
    (h26835 : p85 ∨ p63)
    (h26831 : p45 ∨ p41)
    (h18503 : (¬ p45) ∨ (¬ p85) ∨ (¬ p422) ∨ (¬ p1465)) : (¬ p422) ∨ (¬ p1465) ∨ p63 ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18503 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)

theorem step31589 (p63 p85 p124 p496 p665 p789 p858 p1076 p1077 p1385 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26835 : p85 ∨ p63)
    (h26897 : p858 ∨ p789)
    (h17079 : (¬ p85) ∨ (¬ p124) ∨ (¬ p496) ∨ (¬ p665) ∨ (¬ p858) ∨ (¬ p1077) ∨ (¬ p1385)) : p1076 ∨ (¬ p124) ∨ (¬ p665) ∨ p63 ∨ (¬ p1385) ∨ p789 ∨ (¬ p496) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1076) := fun hu => hn (Or.inl hu)
  have u1 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17079 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u4)

theorem step31590 (p63 p85 p980 p983 p1015 p1055 p1061 p1335 p1385 : Prop)
    (h26903 : p983 ∨ p980)
    (h26909 : p1061 ∨ p1055)
    (h26835 : p85 ∨ p63)
    (h22772 : (¬ p1015) ∨ (¬ p1385) ∨ (¬ p1335) ∨ (¬ p1061) ∨ (¬ p983) ∨ (¬ p85)) : p980 ∨ p1055 ∨ (¬ p1385) ∨ p63 ∨ (¬ p1335) ∨ (¬ p1015) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h22772 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u8)

theorem step31591 (p41 p45 p63 p85 p124 p134 p496 p980 p983 p1076 p1077 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26903 : p983 ∨ p980)
    (h26835 : p85 ∨ p63)
    (h26831 : p45 ∨ p41)
    (h18938 : (¬ p45) ∨ (¬ p85) ∨ (¬ p124) ∨ (¬ p134) ∨ (¬ p496) ∨ (¬ p983) ∨ (¬ p1077)) : p1076 ∨ p980 ∨ p63 ∨ (¬ p124) ∨ (¬ p496) ∨ p41 ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1076) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18938 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u7)

theorem step31593 (p15 p18 p19 p63 p85 p101 p102 : Prop)
    (h26829 : p19 ∨ p18)
    (h26837 : p102 ∨ p101)
    (h26835 : p85 ∨ p63)
    (h16327 : (¬ p15) ∨ (¬ p19) ∨ (¬ p85) ∨ (¬ p102)) : (¬ p15) ∨ p18 ∨ p101 ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p18) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16327 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)

theorem step31594 (p15 p18 p19 p63 p85 p124 p224 p304 p344 p346 p425 p582 : Prop)
    (h26829 : p19 ∨ p18)
    (h26863 : p346 ∨ p344)
    (h26859 : p304 ∨ p124)
    (h26835 : p85 ∨ p63)
    (h16543 : (¬ p15) ∨ (¬ p19) ∨ (¬ p85) ∨ (¬ p224) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p425) ∨ (¬ p582)) : (¬ p425) ∨ (¬ p15) ∨ p18 ∨ p344 ∨ p124 ∨ (¬ p582) ∨ p63 ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h16543 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u5)

theorem step31595 (p15 p63 p85 p234 p424 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h26835 : p85 ∨ p63)
    (h16362 : (¬ p15) ∨ (¬ p85) ∨ (¬ p234) ∨ (¬ p796)) : (¬ p15) ∨ p424 ∨ (¬ p234) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p424) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16362 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step31596 (p41 p45 p63 p85 p163 p167 p1229 : Prop)
    (h26831 : p45 ∨ p41)
    (h26835 : p85 ∨ p63)
    (h26843 : p167 ∨ p163)
    (h16829 : (¬ p45) ∨ (¬ p85) ∨ (¬ p167) ∨ (¬ p1229)) : (¬ p1229) ∨ p41 ∨ p63 ∨ p163 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p41) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16829 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u0)

theorem step31597 (p41 p45 p63 p85 p125 p163 p167 p303 p362 p387 p496 p1325 p1333 : Prop)
    (h26867 : p387 ∨ p303)
    (h26931 : p1333 ∨ p1325)
    (h26831 : p45 ∨ p41)
    (h26843 : p167 ∨ p163)
    (h26835 : p85 ∨ p63)
    (h26865 : p362 ∨ p125)
    (h16320 : (¬ p45) ∨ (¬ p85) ∨ (¬ p167) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p496) ∨ (¬ p1333)) : p303 ∨ p1325 ∨ p41 ∨ (¬ p496) ∨ p163 ∨ p63 ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u12 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h16320 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u11)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u12)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u8)

theorem step31598 (p41 p45 p63 p85 p163 p167 p225 : Prop)
    (h26831 : p45 ∨ p41)
    (h26843 : p167 ∨ p163)
    (h26835 : p85 ∨ p63)
    (h16861 : (¬ p45) ∨ (¬ p85) ∨ (¬ p167) ∨ (¬ p225)) : p41 ∨ p163 ∨ (¬ p225) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p41) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16861 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)

theorem step31599 (p63 p85 p125 p362 p420 p498 p582 : Prop)
    (h26865 : p362 ∨ p125)
    (h26835 : p85 ∨ p63)
    (h16486 : (¬ p85) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p498) ∨ (¬ p582)) : (¬ p498) ∨ (¬ p420) ∨ p125 ∨ p63 ∨ (¬ p582) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16486 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)

theorem step31600 (p63 p85 p227 p496 p1015 p1335 p1385 p1452 : Prop)
    (h26835 : p85 ∨ p63)
    (h16849 : (¬ p85) ∨ (¬ p227) ∨ (¬ p496) ∨ (¬ p1015) ∨ (¬ p1335) ∨ (¬ p1385) ∨ (¬ p1452)) : (¬ p1015) ∨ (¬ p1452) ∨ p63 ∨ (¬ p1385) ∨ (¬ p227) ∨ (¬ p1335) ∨ (¬ p496) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16849 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u1)

theorem step31601 (p63 p85 p227 p455 p456 p498 p582 : Prop)
    (h26871 : p456 ∨ p455)
    (h26835 : p85 ∨ p63)
    (h16832 : (¬ p85) ∨ (¬ p227) ∨ (¬ p456) ∨ (¬ p498) ∨ (¬ p582)) : (¬ p498) ∨ p455 ∨ p63 ∨ (¬ p227) ∨ (¬ p582) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p455) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16832 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)

#print axioms step31601

end NineRUPTrial
