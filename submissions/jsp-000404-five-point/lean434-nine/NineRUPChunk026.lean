import Mathlib.Tactic.Tauto

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

namespace NineRUPTrial

theorem step35720 (p48 p64 p423 p495 p582 p1140 : Prop)
    (h35574 : p582)
    (h27150 : p1140 ∨ (¬ p423) ∨ p495 ∨ (¬ p64) ∨ (¬ p582) ∨ (¬ p48)) : (¬ p423) ∨ p1140 ∨ p495 ∨ (¬ p64) ∨ (¬ p48) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1140) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p582 := by
    exact h35574
  rcases h27150 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u4)

theorem step35723 (p16 p455 p495 p790 p1015 p1335 p1452 : Prop)
    (h35539 : p16)
    (h27164 : (¬ p1452) ∨ (¬ p1015) ∨ p495 ∨ p790 ∨ (¬ p455) ∨ (¬ p16) ∨ (¬ p1335)) : (¬ p1015) ∨ (¬ p1452) ∨ p495 ∨ p790 ∨ (¬ p455) ∨ (¬ p1335) := by
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
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p16 := by
    exact h35539
  rcases h27164 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (u2 q2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u5)

theorem step35724 (p303 p420 p495 p836 p1055 p1103 p1115 : Prop)
    (h35504 : p1103)
    (h27168 : (¬ p1055) ∨ p303 ∨ (¬ p836) ∨ p420 ∨ (¬ p1103) ∨ p1115 ∨ p495) : (¬ p836) ∨ p303 ∨ (¬ p1055) ∨ p420 ∨ p1115 ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1103 := by
    exact h35504
  rcases h27168 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u6)
  · exact False.elim (u4 q5)
  · exact False.elim (u5 q6)

theorem step35726 (p16 p185 p303 p420 p495 p1115 : Prop)
    (h35539 : p16)
    (h27174 : p495 ∨ (¬ p1115) ∨ (¬ p185) ∨ p303 ∨ (¬ p16) ∨ p420) : (¬ p1115) ∨ (¬ p185) ∨ p495 ∨ p303 ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p16 := by
    exact h35539
  rcases h27174 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u5)
  · exact False.elim (u4 q5)

theorem step35727 (p16 p185 p224 p228 p455 p495 p836 : Prop)
    (h35539 : p16)
    (h27175 : (¬ p836) ∨ (¬ p224) ∨ (¬ p455) ∨ p495 ∨ (¬ p185) ∨ (¬ p228) ∨ (¬ p16)) : (¬ p836) ∨ (¬ p455) ∨ (¬ p224) ∨ p495 ∨ (¬ p185) ∨ (¬ p228) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p16 := by
    exact h35539
  rcases h27175 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)

theorem step35728 (p3 p41 p192 p455 p495 p940 p985 p1452 : Prop)
    (h35503 : p985)
    (h27177 : p3 ∨ (¬ p940) ∨ (¬ p1452) ∨ (¬ p192) ∨ (¬ p455) ∨ p495 ∨ (¬ p985) ∨ p41) : (¬ p1452) ∨ (¬ p940) ∨ p3 ∨ (¬ p192) ∨ (¬ p455) ∨ p495 ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p985 := by
    exact h35503
  rcases h27177 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u7)
  · exact False.elim (u6 q7)

theorem step35729 (p12 p225 p303 p420 p495 p1055 p1103 : Prop)
    (h35504 : p1103)
    (h27180 : (¬ p1055) ∨ p495 ∨ (¬ p225) ∨ p303 ∨ (¬ p12) ∨ (¬ p1103) ∨ p420) : p303 ∨ (¬ p1055) ∨ (¬ p225) ∨ p495 ∨ (¬ p12) ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1103 := by
    exact h35504
  rcases h27180 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)
  · exact False.elim (u5 q6)

theorem step35730 (p16 p163 p189 p225 p347 p420 p495 : Prop)
    (h35646 : p347)
    (h35539 : p16)
    (h27181 : (¬ p347) ∨ p495 ∨ p163 ∨ (¬ p189) ∨ (¬ p225) ∨ p420 ∨ (¬ p16)) : p163 ∨ (¬ p225) ∨ p495 ∨ (¬ p189) ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p163) := fun hu => hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p347 := by
    exact h35646
  have u6 : p16 := by
    exact h35539
  rcases h27181 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (u2 q1)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)
  · exact False.elim (u4 q5)
  · exact False.elim (q6 u6)

theorem step35731 (p16 p344 p495 p633 p789 p790 p1325 : Prop)
    (h35539 : p16)
    (h27183 : (¬ p344) ∨ (¬ p633) ∨ (¬ p1325) ∨ p789 ∨ p495 ∨ (¬ p16) ∨ p790) : (¬ p344) ∨ (¬ p633) ∨ (¬ p1325) ∨ p789 ∨ p495 ∨ p790 := by
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
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p16 := by
    exact h35539
  rcases h27183 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u6)
  · exact False.elim (u5 q6)

theorem step35733 (p16 p185 p344 p495 p633 p664 p1115 : Prop)
    (h35539 : p16)
    (h35502 : p664)
    (h27185 : (¬ p1115) ∨ (¬ p344) ∨ (¬ p185) ∨ (¬ p633) ∨ (¬ p16) ∨ p495 ∨ (¬ p664)) : (¬ p1115) ∨ (¬ p344) ∨ (¬ p185) ∨ (¬ p633) ∨ p495 := by
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
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p16 := by
    exact h35539
  have u6 : p664 := by
    exact h35502
  rcases h27185 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)
  · exact False.elim (u4 q5)
  · exact False.elim (q6 u6)

theorem step35734 (p5 p495 p533 p633 p756 p1140 p1465 : Prop)
    (h35501 : p533)
    (h27186 : (¬ p756) ∨ p1140 ∨ (¬ p5) ∨ (¬ p633) ∨ (¬ p1465) ∨ p495 ∨ (¬ p533)) : p1140 ∨ (¬ p756) ∨ (¬ p5) ∨ (¬ p633) ∨ (¬ p1465) ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p533 := by
    exact h35501
  rcases h27186 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)

theorem step35736 (p16 p101 p134 p189 p455 p495 p1084 : Prop)
    (h35539 : p16)
    (h27188 : (¬ p101) ∨ (¬ p1084) ∨ (¬ p189) ∨ p495 ∨ (¬ p134) ∨ (¬ p16) ∨ (¬ p455)) : (¬ p134) ∨ p495 ∨ (¬ p1084) ∨ (¬ p189) ∨ (¬ p101) ∨ (¬ p455) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p16 := by
    exact h35539
  rcases h27188 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u5)

theorem step35737 (p16 p189 p303 p420 p422 p495 p1004 : Prop)
    (h35539 : p16)
    (h27192 : (¬ p422) ∨ (¬ p1004) ∨ p420 ∨ (¬ p189) ∨ (¬ p16) ∨ p495 ∨ p303) : (¬ p422) ∨ (¬ p189) ∨ p420 ∨ (¬ p1004) ∨ p495 ∨ p303 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p16 := by
    exact h35539
  rcases h27192 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (u4 q5)
  · exact False.elim (u5 q6)

theorem step35738 (p17 p574 p633 p668 p836 p918 p1076 : Prop)
    (h35527 : p668)
    (h27202 : (¬ p836) ∨ p17 ∨ p1076 ∨ (¬ p918) ∨ (¬ p633) ∨ (¬ p574) ∨ (¬ p668)) : (¬ p836) ∨ p17 ∨ p1076 ∨ (¬ p918) ∨ (¬ p633) ∨ (¬ p574) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p574 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p668 := by
    exact h35527
  rcases h27202 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)

theorem step35739 (p156 p192 p382 p477 p918 p1286 p1392 : Prop)
    (h35659 : p156)
    (h18953 : (¬ p156) ∨ (¬ p192) ∨ (¬ p382) ∨ (¬ p477) ∨ (¬ p918) ∨ (¬ p1286) ∨ (¬ p1392)) : (¬ p918) ∨ (¬ p477) ∨ (¬ p382) ∨ (¬ p1286) ∨ (¬ p192) ∨ (¬ p1392) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p477 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1392 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p156 := by
    exact h35659
  rcases h18953 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u5)

theorem step35740 (p156 p192 p206 p455 p580 p918 p961 : Prop)
    (h35659 : p156)
    (h19724 : (¬ p156) ∨ (¬ p192) ∨ (¬ p206) ∨ (¬ p455) ∨ (¬ p580) ∨ (¬ p918) ∨ (¬ p961)) : (¬ p918) ∨ (¬ p580) ∨ (¬ p961) ∨ (¬ p455) ∨ (¬ p192) ∨ (¬ p206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p580 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p455 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p156 := by
    exact h35659
  rcases h19724 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u2)

theorem step35741 (p3 p41 p166 p195 p918 : Prop)
    (h35556 : p195)
    (h18098 : (¬ p3) ∨ (¬ p41) ∨ (¬ p166) ∨ (¬ p195) ∨ (¬ p918)) : (¬ p918) ∨ (¬ p3) ∨ (¬ p41) ∨ (¬ p166) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p918 := by
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
  have u3 : p166 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p195 := by
    exact h35556
  rcases h18098 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u0)

theorem step35743 (p3 p63 p225 p664 p918 p1115 : Prop)
    (h35502 : p664)
    (h27217 : (¬ p1115) ∨ (¬ p3) ∨ p63 ∨ (¬ p918) ∨ p225 ∨ (¬ p664)) : (¬ p1115) ∨ (¬ p3) ∨ p63 ∨ (¬ p918) ∨ p225 := by
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
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p664 := by
    exact h35502
  rcases h27217 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u5)

theorem step35745 (p63 p224 p290 p344 p368 p382 p496 p918 : Prop)
    (h35500 : p496)
    (h27226 : p382 ∨ (¬ p918) ∨ (¬ p368) ∨ p63 ∨ (¬ p496) ∨ (¬ p224) ∨ p344 ∨ (¬ p290)) : (¬ p918) ∨ p382 ∨ (¬ p368) ∨ p63 ∨ (¬ p224) ∨ p344 ∨ (¬ p290) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p290 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p496 := by
    exact h35500
  rcases h27226 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u6)

theorem step35746 (p6 p18 p48 p156 p192 p918 : Prop)
    (h35659 : p156)
    (h27232 : p18 ∨ (¬ p48) ∨ (¬ p192) ∨ (¬ p6) ∨ (¬ p156) ∨ (¬ p918)) : (¬ p918) ∨ (¬ p192) ∨ p18 ∨ (¬ p48) ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p156 := by
    exact h35659
  rcases h27232 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u0)

theorem step35748 (p227 p331 p382 p419 p420 p455 p498 p621 : Prop)
    (h35686 : p331)
    (h27252 : p455 ∨ (¬ p498) ∨ p419 ∨ (¬ p331) ∨ p420 ∨ (¬ p227) ∨ (¬ p382) ∨ (¬ p621)) : p455 ∨ p419 ∨ (¬ p498) ∨ p420 ∨ (¬ p227) ∨ (¬ p382) ∨ (¬ p621) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p419) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p621 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p331 := by
    exact h35686
  rcases h27252 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u7)
  · exact False.elim (u3 q4)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step35750 (p16 p124 p344 p498 p728 p1330 p1349 p1489 : Prop)
    (h35539 : p16)
    (h19465 : (¬ p16) ∨ (¬ p124) ∨ (¬ p344) ∨ (¬ p498) ∨ (¬ p728) ∨ (¬ p1330) ∨ (¬ p1349) ∨ (¬ p1489)) : (¬ p1489) ∨ (¬ p728) ∨ (¬ p498) ∨ (¬ p344) ∨ (¬ p1349) ∨ (¬ p124) ∨ (¬ p1330) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p16 := by
    exact h35539
  rcases h19465 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u0)

theorem step35751 (p16 p124 p189 p331 p420 p424 p498 p633 : Prop)
    (h35539 : p16)
    (h35686 : p331)
    (h27257 : (¬ p498) ∨ p424 ∨ p633 ∨ (¬ p16) ∨ (¬ p189) ∨ (¬ p124) ∨ p420 ∨ (¬ p331)) : p424 ∨ p633 ∨ (¬ p498) ∨ (¬ p189) ∨ (¬ p124) ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p633) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p16 := by
    exact h35539
  have u7 : p331 := by
    exact h35686
  rcases h27257 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u7)

theorem step35753 (p16 p185 p227 p347 p420 p455 p498 p836 : Prop)
    (h35646 : p347)
    (h35539 : p16)
    (h27263 : (¬ p498) ∨ (¬ p836) ∨ (¬ p185) ∨ (¬ p227) ∨ p420 ∨ (¬ p347) ∨ p455 ∨ (¬ p16)) : (¬ p836) ∨ p455 ∨ (¬ p185) ∨ (¬ p227) ∨ p420 ∨ (¬ p498) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p455) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p347 := by
    exact h35646
  have u7 : p16 := by
    exact h35539
  rcases h27263 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u6)
  · exact False.elim (u1 q6)
  · exact False.elim (q7 u7)

theorem step35754 (p16 p110 p125 p163 p189 p420 p498 p633 : Prop)
    (h35539 : p16)
    (h27264 : (¬ p420) ∨ (¬ p110) ∨ (¬ p633) ∨ p163 ∨ (¬ p16) ∨ (¬ p498) ∨ (¬ p189) ∨ p125) : p163 ∨ (¬ p420) ∨ (¬ p633) ∨ (¬ p110) ∨ (¬ p498) ∨ (¬ p189) ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p163) := fun hu => hn (Or.inl hu)
  have u1 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p16 := by
    exact h35539
  rcases h27264 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (u6 q7)

theorem step35756 (p10 p121 p185 p224 p227 p263 p836 : Prop)
    (h35554 : p263)
    (h27289 : p121 ∨ (¬ p836) ∨ p10 ∨ (¬ p263) ∨ (¬ p227) ∨ (¬ p224) ∨ (¬ p185)) : p10 ∨ (¬ p836) ∨ p121 ∨ (¬ p227) ∨ (¬ p224) ∨ (¬ p185) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p10) := fun hu => hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p121) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p263 := by
    exact h35554
  rcases h27289 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step35757 (p6 p10 p163 p195 p224 p347 p382 p560 p709 : Prop)
    (h35556 : p195)
    (h35646 : p347)
    (h27294 : (¬ p560) ∨ p163 ∨ p10 ∨ (¬ p709) ∨ (¬ p382) ∨ p6 ∨ (¬ p195) ∨ p224 ∨ (¬ p347)) : p10 ∨ (¬ p560) ∨ p163 ∨ (¬ p709) ∨ (¬ p382) ∨ p6 ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p10) := fun hu => hn (Or.inl hu)
  have u1 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p709 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p195 := by
    exact h35556
  have u8 : p347 := by
    exact h35646
  rcases h27294 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u1)
  · exact False.elim (u2 q1)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u7)
  · exact False.elim (u6 q7)
  · exact False.elim (q8 u8)

theorem step35758 (p10 p39 p63 p68 p101 p124 p211 p595 p603 : Prop)
    (h35495 : p39)
    (h27302 : p595 ∨ (¬ p101) ∨ (¬ p211) ∨ (¬ p603) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p124) ∨ p10 ∨ (¬ p68)) : (¬ p603) ∨ p595 ∨ (¬ p211) ∨ (¬ p101) ∨ (¬ p63) ∨ (¬ p124) ∨ p10 ∨ (¬ p68) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p603 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p595) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p39 := by
    exact h35495
  rcases h27302 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (u6 q7)
  · exact False.elim (q8 u7)

theorem step35769 (p3 p163 p188 p303 p331 p382 p424 p817 : Prop)
    (h35686 : p331)
    (h27364 : p3 ∨ p424 ∨ p382 ∨ (¬ p188) ∨ (¬ p817) ∨ (¬ p303) ∨ (¬ p163) ∨ (¬ p331)) : p424 ∨ p382 ∨ p3 ∨ (¬ p188) ∨ (¬ p817) ∨ (¬ p303) ∨ (¬ p163) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p817 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p331 := by
    exact h35686
  rcases h27364 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u7)

theorem step35770 (p17 p138 p186 p422 p1140 : Prop)
    (h35668 : p138)
    (h17466 : (¬ p17) ∨ (¬ p138) ∨ (¬ p186) ∨ (¬ p422) ∨ (¬ p1140)) : (¬ p1140) ∨ (¬ p422) ∨ (¬ p17) ∨ (¬ p186) := by
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
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p138 := by
    exact h35668
  rcases h17466 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)

theorem step35771 (p6 p11 p17 p101 p156 p185 p192 p1084 : Prop)
    (h35659 : p156)
    (h27393 : (¬ p185) ∨ p11 ∨ (¬ p156) ∨ (¬ p192) ∨ (¬ p1084) ∨ (¬ p6) ∨ p17 ∨ (¬ p101)) : p11 ∨ (¬ p185) ∨ (¬ p192) ∨ (¬ p1084) ∨ (¬ p6) ∨ p17 ∨ (¬ p101) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p11) := fun hu => hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p156 := by
    exact h35659
  rcases h27393 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u6)

theorem step35772 (p124 p126 p258 p261 p327 p382 p419 p817 : Prop)
    (h35549 : p327)
    (h27420 : p126 ∨ (¬ p327) ∨ (¬ p261) ∨ (¬ p419) ∨ (¬ p817) ∨ p124 ∨ p382 ∨ p258) : (¬ p419) ∨ p126 ∨ (¬ p261) ∨ (¬ p817) ∨ p124 ∨ p382 ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p817 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p327 := by
    exact h35549
  rcases h27420 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u3)
  · exact False.elim (u4 q5)
  · exact False.elim (u5 q6)
  · exact False.elim (u6 q7)

theorem step35773 (p124 p126 p258 p261 p327 p435 p687 p817 : Prop)
    (h35549 : p327)
    (h27421 : p124 ∨ p126 ∨ (¬ p435) ∨ (¬ p687) ∨ (¬ p261) ∨ (¬ p327) ∨ (¬ p817) ∨ p258) : (¬ p435) ∨ p126 ∨ p124 ∨ (¬ p687) ∨ (¬ p261) ∨ (¬ p817) ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p817 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p327 := by
    exact h35549
  rcases h27421 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u5)
  · exact False.elim (u6 q7)

theorem step35774 (p124 p125 p258 p331 p419 p789 p790 : Prop)
    (h35686 : p331)
    (h27422 : p419 ∨ p124 ∨ p790 ∨ p125 ∨ p258 ∨ (¬ p331) ∨ p789) : p790 ∨ p124 ∨ p419 ∨ p125 ∨ p258 ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p790) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p331 := by
    exact h35686
  rcases h27422 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (u0 q2)
  · exact False.elim (u3 q3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u6)
  · exact False.elim (u5 q6)

theorem step35775 (p124 p135 p185 p189 p265 p344 p668 p1115 : Prop)
    (h35527 : p668)
    (h27423 : p124 ∨ (¬ p265) ∨ p185 ∨ (¬ p135) ∨ p344 ∨ p1115 ∨ (¬ p189) ∨ (¬ p668)) : p124 ∨ (¬ p265) ∨ p185 ∨ (¬ p135) ∨ p344 ∨ p1115 ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p668 := by
    exact h35527
  rcases h27423 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u7)

theorem step35776 (p11 p17 p87 p455 p580 : Prop)
    (h35497 : p87)
    (h19631 : (¬ p11) ∨ (¬ p17) ∨ (¬ p87) ∨ (¬ p455) ∨ (¬ p580)) : (¬ p580) ∨ (¬ p11) ∨ (¬ p455) ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p580 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p87 := by
    exact h35497
  rcases h19631 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u0)

theorem step35777 (p11 p15 p17 p39 p88 p389 p419 p595 p1192 : Prop)
    (h35495 : p39)
    (h27429 : (¬ p389) ∨ (¬ p11) ∨ (¬ p595) ∨ (¬ p17) ∨ (¬ p88) ∨ p15 ∨ (¬ p1192) ∨ (¬ p39) ∨ p419) : (¬ p389) ∨ (¬ p88) ∨ (¬ p595) ∨ (¬ p17) ∨ (¬ p11) ∨ p15 ∨ (¬ p1192) ∨ p419 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p39 := by
    exact h35495
  rcases h27429 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u8)
  · exact False.elim (u7 q8)

theorem step35778 (p2 p11 p17 p39 p68 p88 p532 p1330 p1366 : Prop)
    (h35495 : p39)
    (h27430 : (¬ p1366) ∨ (¬ p11) ∨ (¬ p39) ∨ (¬ p17) ∨ (¬ p88) ∨ p2 ∨ (¬ p68) ∨ (¬ p1330) ∨ (¬ p532)) : (¬ p88) ∨ (¬ p11) ∨ (¬ p17) ∨ (¬ p1366) ∨ p2 ∨ (¬ p68) ∨ (¬ p1330) ∨ (¬ p532) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p88 := by
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
  have u3 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p39 := by
    exact h35495
  rcases h27430 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u0)
  · exact False.elim (u4 q5)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step35780 (p3 p11 p17 p190 p532 p533 p534 : Prop)
    (h35501 : p533)
    (h17743 : (¬ p3) ∨ (¬ p11) ∨ (¬ p17) ∨ (¬ p190) ∨ (¬ p532) ∨ (¬ p533) ∨ (¬ p534)) : (¬ p534) ∨ (¬ p3) ∨ (¬ p17) ∨ (¬ p532) ∨ (¬ p190) ∨ (¬ p11) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p3 := by
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
  have u4 : p190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p533 := by
    exact h35501
  rcases h17743 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u0)

theorem step35781 (p11 p136 p156 p185 p227 p266 : Prop)
    (h35659 : p156)
    (h18368 : (¬ p11) ∨ (¬ p136) ∨ (¬ p156) ∨ (¬ p185) ∨ (¬ p227) ∨ (¬ p266)) : (¬ p227) ∨ (¬ p11) ∨ (¬ p185) ∨ (¬ p136) ∨ (¬ p266) := by
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
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p136 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p156 := by
    exact h35659
  rcases h18368 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u4)

theorem step35782 (p11 p16 p17 p532 p595 p1330 p1542 : Prop)
    (h35539 : p16)
    (h19555 : (¬ p11) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p532) ∨ (¬ p595) ∨ (¬ p1330) ∨ (¬ p1542)) : (¬ p1542) ∨ (¬ p532) ∨ (¬ p11) ∨ (¬ p595) ∨ (¬ p1330) ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p11 := by
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
  have u5 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p16 := by
    exact h35539
  rcases h19555 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u0)

theorem step35788 (p17 p241 p344 p574 p633 p664 p918 p1055 : Prop)
    (h35502 : p664)
    (h27492 : (¬ p241) ∨ (¬ p1055) ∨ (¬ p574) ∨ (¬ p664) ∨ (¬ p633) ∨ (¬ p344) ∨ p17 ∨ (¬ p918)) : (¬ p344) ∨ (¬ p1055) ∨ (¬ p574) ∨ (¬ p633) ∨ (¬ p241) ∨ p17 ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1055 := by
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
  have u4 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p664 := by
    exact h35502
  rcases h27492 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u0)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u6)

theorem step35789 (p86 p185 p495 p633 p664 p836 p1076 : Prop)
    (h35496 : p86)
    (h35502 : p664)
    (h27517 : p633 ∨ (¬ p1076) ∨ p836 ∨ (¬ p495) ∨ (¬ p86) ∨ p185 ∨ (¬ p664)) : p836 ∨ p633 ∨ (¬ p1076) ∨ (¬ p495) ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p836) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p633) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p86 := by
    exact h35496
  have u6 : p664 := by
    exact h35502
  rcases h27517 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)
  · exact False.elim (u4 q5)
  · exact False.elim (q6 u6)

theorem step35790 (p17 p87 p126 p420 p580 : Prop)
    (h35497 : p87)
    (h27537 : p126 ∨ (¬ p580) ∨ (¬ p87) ∨ p420 ∨ (¬ p17)) : p420 ∨ p126 ∨ (¬ p580) ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p420) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p580 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p87 := by
    exact h35497
  rcases h27537 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u3)

theorem step35791 (p16 p17 p126 p303 p665 p1095 p1096 : Prop)
    (h35539 : p16)
    (h27538 : (¬ p303) ∨ p126 ∨ (¬ p17) ∨ (¬ p16) ∨ (¬ p1096) ∨ (¬ p665) ∨ (¬ p1095)) : p126 ∨ (¬ p303) ∨ (¬ p17) ∨ (¬ p1096) ∨ (¬ p665) ∨ (¬ p1095) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p16 := by
    exact h35539
  rcases h27538 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step35792 (p16 p17 p126 p161 p438 p1229 p1335 : Prop)
    (h35539 : p16)
    (h27539 : (¬ p438) ∨ p126 ∨ p161 ∨ (¬ p1229) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p1335)) : p161 ∨ p126 ∨ (¬ p438) ∨ (¬ p1229) ∨ (¬ p17) ∨ (¬ p1335) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p161) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p16 := by
    exact h35539
  rcases h27539 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (u1 q1)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step35794 (p17 p87 p126 p382 p431 p438 p816 p1385 : Prop)
    (h35497 : p87)
    (h27541 : p126 ∨ (¬ p438) ∨ (¬ p87) ∨ p1385 ∨ (¬ p431) ∨ p382 ∨ (¬ p17) ∨ (¬ p816)) : p1385 ∨ p126 ∨ (¬ p438) ∨ (¬ p431) ∨ p382 ∨ (¬ p17) ∨ (¬ p816) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1385) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p816 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p87 := by
    exact h35497
  rcases h27541 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u7)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (u4 q5)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step35795 (p16 p17 p126 p224 p351 p595 p1286 : Prop)
    (h35539 : p16)
    (h27543 : (¬ p595) ∨ p126 ∨ (¬ p17) ∨ (¬ p351) ∨ (¬ p224) ∨ (¬ p1286) ∨ (¬ p16)) : p126 ∨ (¬ p595) ∨ (¬ p17) ∨ (¬ p351) ∨ (¬ p224) ∨ (¬ p1286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p16 := by
    exact h35539
  rcases h27543 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)

theorem step35796 (p9 p16 p17 p126 p303 p897 p1055 p1074 : Prop)
    (h35539 : p16)
    (h27544 : p126 ∨ (¬ p303) ∨ (¬ p1074) ∨ (¬ p9) ∨ p1055 ∨ (¬ p17) ∨ p897 ∨ (¬ p16)) : p126 ∨ (¬ p1074) ∨ (¬ p303) ∨ (¬ p9) ∨ p1055 ∨ (¬ p17) ∨ p897 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p9 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p16 := by
    exact h35539
  rcases h27544 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)
  · exact False.elim (q7 u7)

theorem step35797 (p14 p15 p16 p17 p126 p225 p351 : Prop)
    (h35539 : p16)
    (h27545 : p126 ∨ p225 ∨ (¬ p14) ∨ (¬ p17) ∨ (¬ p15) ∨ (¬ p351) ∨ (¬ p16)) : (¬ p14) ∨ p126 ∨ p225 ∨ (¬ p17) ∨ (¬ p15) ∨ (¬ p351) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p16 := by
    exact h35539
  rcases h27545 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)

theorem step35798 (p15 p16 p17 p126 p303 p423 p1000 : Prop)
    (h35539 : p16)
    (h27546 : p126 ∨ (¬ p15) ∨ (¬ p303) ∨ (¬ p423) ∨ (¬ p1000) ∨ (¬ p17) ∨ (¬ p16)) : p126 ∨ (¬ p303) ∨ (¬ p15) ∨ (¬ p423) ∨ (¬ p1000) ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p16 := by
    exact h35539
  rcases h27546 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)

theorem step35799 (p15 p17 p39 p88 p126 p225 p303 p883 p1096 : Prop)
    (h35495 : p39)
    (h27548 : p225 ∨ (¬ p883) ∨ (¬ p88) ∨ (¬ p39) ∨ p126 ∨ p15 ∨ (¬ p303) ∨ (¬ p17) ∨ (¬ p1096)) : (¬ p883) ∨ (¬ p88) ∨ p225 ∨ p126 ∨ p15 ∨ (¬ p303) ∨ (¬ p17) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p883 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p126) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p39 := by
    exact h35495
  rcases h27548 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u8)
  · exact False.elim (u3 q4)
  · exact False.elim (u4 q5)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step35800 (p15 p17 p39 p88 p126 p303 p1000 p1145 p1229 : Prop)
    (h35495 : p39)
    (h27549 : p126 ∨ (¬ p88) ∨ (¬ p1145) ∨ (¬ p303) ∨ p15 ∨ (¬ p39) ∨ (¬ p1000) ∨ (¬ p17) ∨ (¬ p1229)) : (¬ p1145) ∨ p126 ∨ (¬ p88) ∨ (¬ p303) ∨ p15 ∨ (¬ p1000) ∨ (¬ p17) ∨ (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1145 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p39 := by
    exact h35495
  rcases h27549 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step35801 (p327 p386 p419 p1325 p1452 : Prop)
    (h35549 : p327)
    (h17673 : (¬ p327) ∨ (¬ p386) ∨ (¬ p419) ∨ (¬ p1325) ∨ (¬ p1452)) : (¬ p386) ∨ (¬ p1452) ∨ (¬ p1325) ∨ (¬ p419) := by
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
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p327 := by
    exact h35549
  rcases h17673 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u1)

theorem step35802 (p227 p496 p1074 p1096 p1325 p1452 : Prop)
    (h35500 : p496)
    (h27590 : (¬ p1452) ∨ (¬ p496) ∨ (¬ p1074) ∨ (¬ p227) ∨ p1096 ∨ (¬ p1325)) : (¬ p1452) ∨ (¬ p1074) ∨ (¬ p1325) ∨ (¬ p227) ∨ p1096 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p496 := by
    exact h35500
  rcases h27590 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u2)

theorem step35804 (p125 p189 p263 p422 p434 p1330 p1465 : Prop)
    (h35554 : p263)
    (h27602 : (¬ p422) ∨ (¬ p434) ∨ (¬ p189) ∨ (¬ p1330) ∨ (¬ p263) ∨ p125 ∨ (¬ p1465)) : (¬ p434) ∨ (¬ p422) ∨ (¬ p189) ∨ (¬ p1330) ∨ p125 ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p263 := by
    exact h35554
  rcases h27602 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (u4 q5)
  · exact False.elim (q6 u5)

theorem step35805 (p124 p189 p263 p422 p533 p756 p1465 : Prop)
    (h35554 : p263)
    (h35501 : p533)
    (h18178 : (¬ p124) ∨ (¬ p189) ∨ (¬ p263) ∨ (¬ p422) ∨ (¬ p533) ∨ (¬ p756) ∨ (¬ p1465)) : (¬ p756) ∨ (¬ p422) ∨ (¬ p124) ∨ (¬ p1465) ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p263 := by
    exact h35554
  have u6 : p533 := by
    exact h35501
  rcases h18178 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u3)

theorem step35806 (p101 p121 p344 p664 p1079 : Prop)
    (h35502 : p664)
    (h27610 : p121 ∨ (¬ p1079) ∨ (¬ p664) ∨ p101 ∨ (¬ p344)) : (¬ p344) ∨ p101 ∨ (¬ p1079) ∨ p121 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p101) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1079 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p121) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p664 := by
    exact h35502
  rcases h27610 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u0)

theorem step35807 (p16 p71 p185 p423 p980 p1115 p1710 p1805 : Prop)
    (h35539 : p16)
    (h17713 : (¬ p16) ∨ (¬ p71) ∨ (¬ p185) ∨ (¬ p423) ∨ (¬ p980) ∨ (¬ p1115) ∨ (¬ p1710) ∨ (¬ p1805)) : (¬ p1805) ∨ (¬ p1710) ∨ (¬ p185) ∨ (¬ p980) ∨ (¬ p1115) ∨ (¬ p423) ∨ (¬ p71) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1805 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1710 := by
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
  have u5 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p16 := by
    exact h35539
  rcases h17713 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u0)

theorem step35808 (p234 p303 p331 p423 p1001 : Prop)
    (h35686 : p331)
    (h27663 : p234 ∨ (¬ p423) ∨ (¬ p303) ∨ (¬ p331) ∨ (¬ p1001)) : (¬ p423) ∨ p234 ∨ (¬ p303) ∨ (¬ p1001) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p234) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1001 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p331 := by
    exact h35686
  rcases h27663 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)

theorem step35809 (p16 p17 p18 p258 p344 p382 p620 p1188 p1287 : Prop)
    (h35539 : p16)
    (h27679 : (¬ p1188) ∨ (¬ p620) ∨ (¬ p16) ∨ p18 ∨ (¬ p1287) ∨ (¬ p258) ∨ p344 ∨ p382 ∨ (¬ p17)) : p382 ∨ (¬ p620) ∨ p18 ∨ (¬ p1287) ∨ (¬ p258) ∨ p344 ∨ (¬ p1188) ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p620 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p16 := by
    exact h35539
  rcases h27679 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u8)
  · exact False.elim (u2 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)
  · exact False.elim (u0 q7)
  · exact False.elim (q8 u7)

theorem step35810 (p9 p16 p17 p18 p126 p303 p879 p1055 p1074 : Prop)
    (h35539 : p16)
    (h27680 : p126 ∨ (¬ p1074) ∨ (¬ p303) ∨ p18 ∨ (¬ p17) ∨ (¬ p9) ∨ (¬ p16) ∨ (¬ p879) ∨ p1055) : p126 ∨ (¬ p1074) ∨ (¬ p303) ∨ p18 ∨ (¬ p17) ∨ (¬ p9) ∨ (¬ p879) ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p9 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p879 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p16 := by
    exact h35539
  rcases h27680 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u6)
  · exact False.elim (u7 q8)

theorem step35811 (p3 p14 p16 p17 p18 p71 p126 p303 : Prop)
    (h35539 : p16)
    (h27681 : p14 ∨ (¬ p3) ∨ (¬ p16) ∨ p126 ∨ (¬ p71) ∨ (¬ p17) ∨ (¬ p303) ∨ p18) : p14 ∨ (¬ p3) ∨ p126 ∨ (¬ p71) ∨ (¬ p17) ∨ (¬ p303) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p126) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p16 := by
    exact h35539
  rcases h27681 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u7)
  · exact False.elim (u2 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (u6 q7)

theorem step35812 (p16 p18 p71 p125 p126 p143 p261 p423 p1140 : Prop)
    (h35539 : p16)
    (h27683 : p423 ∨ (¬ p125) ∨ p18 ∨ (¬ p1140) ∨ (¬ p143) ∨ (¬ p126) ∨ (¬ p261) ∨ (¬ p16) ∨ (¬ p71)) : (¬ p1140) ∨ p423 ∨ p18 ∨ (¬ p125) ∨ (¬ p143) ∨ (¬ p126) ∨ (¬ p261) ∨ (¬ p71) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p423) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p143 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p16 := by
    exact h35539
  rcases h27683 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u7)

theorem step35813 (p16 p18 p71 p185 p224 p423 p836 p1140 : Prop)
    (h35539 : p16)
    (h27684 : (¬ p836) ∨ p423 ∨ (¬ p16) ∨ (¬ p224) ∨ p18 ∨ (¬ p71) ∨ (¬ p185) ∨ (¬ p1140)) : p423 ∨ (¬ p836) ∨ (¬ p224) ∨ p18 ∨ (¬ p71) ∨ (¬ p185) ∨ (¬ p1140) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p16 := by
    exact h35539
  rcases h27684 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u2)
  · exact False.elim (u3 q4)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step35814 (p6 p18 p64 p86 p234 p789 p790 p1325 : Prop)
    (h35496 : p86)
    (h27688 : (¬ p789) ∨ p1325 ∨ p18 ∨ (¬ p790) ∨ p234 ∨ (¬ p86) ∨ (¬ p64) ∨ (¬ p6)) : (¬ p790) ∨ (¬ p789) ∨ p1325 ∨ p18 ∨ p234 ∨ (¬ p64) ∨ (¬ p6) := by
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
  have u2 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p234) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p86 := by
    exact h35496
  rcases h27688 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (u2 q1)
  · exact False.elim (u3 q2)
  · exact False.elim (q3 u0)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step35815 (p6 p18 p64 p86 p185 p234 p545 p836 : Prop)
    (h35496 : p86)
    (h27690 : p234 ∨ (¬ p545) ∨ (¬ p86) ∨ p18 ∨ (¬ p64) ∨ (¬ p6) ∨ p836 ∨ p185) : p836 ∨ (¬ p6) ∨ p18 ∨ p234 ∨ (¬ p64) ∨ (¬ p545) ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p836) := fun hu => hn (Or.inl hu)
  have u1 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p234) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p86 := by
    exact h35496
  rcases h27690 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u7)
  · exact False.elim (u2 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u1)
  · exact False.elim (u0 q6)
  · exact False.elim (u6 q7)

theorem step35816 (p18 p48 p87 p134 p189 : Prop)
    (h35497 : p87)
    (h27695 : (¬ p189) ∨ p18 ∨ (¬ p134) ∨ (¬ p87) ∨ (¬ p48)) : (¬ p134) ∨ (¬ p189) ∨ p18 ∨ (¬ p48) := by
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
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p87 := by
    exact h35497
  rcases h27695 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)

theorem step35817 (p8 p15 p18 p121 p224 p228 p1103 : Prop)
    (h35504 : p1103)
    (h27700 : (¬ p15) ∨ (¬ p121) ∨ (¬ p224) ∨ (¬ p228) ∨ p18 ∨ (¬ p1103) ∨ p8) : (¬ p121) ∨ p8 ∨ (¬ p224) ∨ (¬ p228) ∨ (¬ p15) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p8) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1103 := by
    exact h35504
  rcases h27700 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u6)
  · exact False.elim (u1 q6)

theorem step35818 (p15 p18 p101 p290 p1055 p1103 p1115 : Prop)
    (h35504 : p1103)
    (h27708 : (¬ p15) ∨ (¬ p290) ∨ p101 ∨ (¬ p1055) ∨ (¬ p1103) ∨ p1115 ∨ p18) : (¬ p290) ∨ p101 ∨ p18 ∨ (¬ p1055) ∨ p1115 ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p290 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p101) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1103 := by
    exact h35504
  rcases h27708 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u0)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (u4 q5)
  · exact False.elim (u2 q6)

theorem step35819 (p18 p125 p207 p234 p347 p540 : Prop)
    (h35646 : p347)
    (h27728 : p234 ∨ p18 ∨ (¬ p207) ∨ (¬ p347) ∨ (¬ p540) ∨ p125) : (¬ p207) ∨ (¬ p540) ∨ p18 ∨ p234 ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p540 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p234) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p347 := by
    exact h35646
  rcases h27728 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)
  · exact False.elim (u4 q5)

theorem step35820 (p6 p14 p18 p156 p185 p192 p789 p790 : Prop)
    (h35659 : p156)
    (h27736 : (¬ p789) ∨ p18 ∨ (¬ p6) ∨ (¬ p192) ∨ p14 ∨ (¬ p156) ∨ (¬ p185) ∨ (¬ p790)) : p14 ∨ (¬ p192) ∨ (¬ p6) ∨ p18 ∨ (¬ p789) ∨ (¬ p185) ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p156 := by
    exact h35659
  rcases h27736 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u4)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (u0 q4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step35821 (p15 p18 p980 p1055 p1103 p1449 p1665 : Prop)
    (h35504 : p1103)
    (h27738 : (¬ p1665) ∨ (¬ p15) ∨ (¬ p1449) ∨ (¬ p980) ∨ (¬ p1055) ∨ p18 ∨ (¬ p1103)) : (¬ p1449) ∨ (¬ p1665) ∨ p18 ∨ (¬ p980) ∨ (¬ p1055) ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1449 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1103 := by
    exact h35504
  rcases h27738 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (u2 q5)
  · exact False.elim (q6 u6)

theorem step35822 (p10 p15 p18 p224 p347 p382 p621 : Prop)
    (h35646 : p347)
    (h27745 : (¬ p15) ∨ (¬ p347) ∨ p10 ∨ p18 ∨ (¬ p621) ∨ (¬ p382) ∨ p224) : (¬ p382) ∨ p224 ∨ p10 ∨ (¬ p15) ∨ (¬ p621) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p621 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p347 := by
    exact h35646
  rcases h27745 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (u2 q2)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u0)
  · exact False.elim (u1 q6)

theorem step35824 (p1 p12 p15 p124 p234 p344 p496 p664 : Prop)
    (h35500 : p496)
    (h35502 : p664)
    (h27794 : p234 ∨ (¬ p1) ∨ (¬ p496) ∨ (¬ p664) ∨ p15 ∨ (¬ p124) ∨ p12 ∨ (¬ p344)) : p15 ∨ (¬ p1) ∨ p234 ∨ (¬ p124) ∨ p12 ∨ (¬ p344) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p15) := fun hu => hn (Or.inl hu)
  have u1 : p1 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p234) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p496 := by
    exact h35500
  have u7 : p664 := by
    exact h35502
  rcases h27794 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (u0 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (u4 q6)
  · exact False.elim (q7 u5)

theorem step35850 (p10 p39 p63 p68 p101 p125 p211 p897 p1096 : Prop)
    (h35495 : p39)
    (h27828 : p125 ∨ (¬ p10) ∨ (¬ p897) ∨ p1096 ∨ p101 ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p211) ∨ (¬ p68)) : (¬ p10) ∨ (¬ p897) ∨ p125 ∨ p1096 ∨ p101 ∨ (¬ p63) ∨ (¬ p211) ∨ (¬ p68) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p39 := by
    exact h35495
  rcases h27828 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u3 q3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step35851 (p86 p124 p389 p455 p494 p633 p789 p790 : Prop)
    (h35496 : p86)
    (h27838 : (¬ p789) ∨ (¬ p790) ∨ (¬ p389) ∨ (¬ p633) ∨ p124 ∨ (¬ p86) ∨ (¬ p494) ∨ p455) : (¬ p790) ∨ p124 ∨ (¬ p389) ∨ (¬ p633) ∨ (¬ p789) ∨ (¬ p494) ∨ p455 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p455) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p86 := by
    exact h35496
  rcases h27838 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (u1 q4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u5)
  · exact False.elim (u6 q7)

theorem step35852 (p13 p86 p125 p185 p420 p455 p494 p1115 : Prop)
    (h35496 : p86)
    (h27839 : p455 ∨ p420 ∨ (¬ p494) ∨ (¬ p13) ∨ p1115 ∨ p185 ∨ (¬ p125) ∨ (¬ p86)) : p455 ∨ (¬ p494) ∨ p420 ∨ (¬ p13) ∨ p1115 ∨ p185 ∨ (¬ p125) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p86 := by
    exact h35496
  rcases h27839 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u7)

theorem step35853 (p86 p124 p189 p327 p420 p424 p494 p633 : Prop)
    (h35549 : p327)
    (h35496 : p86)
    (h27840 : (¬ p420) ∨ p124 ∨ (¬ p327) ∨ (¬ p424) ∨ (¬ p633) ∨ (¬ p494) ∨ p189 ∨ (¬ p86)) : (¬ p420) ∨ (¬ p633) ∨ p124 ∨ (¬ p424) ∨ (¬ p494) ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p327 := by
    exact h35549
  have u7 : p86 := by
    exact h35496
  rcases h27840 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u7)

theorem step35854 (p8 p63 p305 p425 p431 p582 p595 p734 p1286 : Prop)
    (h35574 : p582)
    (h27850 : (¬ p305) ∨ (¬ p431) ∨ (¬ p425) ∨ (¬ p595) ∨ p8 ∨ (¬ p734) ∨ p63 ∨ (¬ p1286) ∨ (¬ p582)) : (¬ p305) ∨ (¬ p1286) ∨ (¬ p425) ∨ (¬ p595) ∨ p8 ∨ (¬ p734) ∨ p63 ∨ (¬ p431) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p582 := by
    exact h35574
  rcases h27850 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u8)

theorem step35855 (p124 p344 p425 p582 p897 p927 : Prop)
    (h35574 : p582)
    (h27851 : p124 ∨ (¬ p927) ∨ p897 ∨ p344 ∨ (¬ p582) ∨ (¬ p425)) : p897 ∨ (¬ p927) ∨ p124 ∨ p344 ∨ (¬ p425) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p897) := fun hu => hn (Or.inl hu)
  have u1 : p927 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p582 := by
    exact h35574
  rcases h27851 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (u0 q2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u4)

theorem step35856 (p63 p125 p303 p425 p582 p665 p1095 p1096 : Prop)
    (h35574 : p582)
    (h27852 : (¬ p125) ∨ (¬ p1095) ∨ (¬ p425) ∨ p63 ∨ (¬ p582) ∨ (¬ p665) ∨ (¬ p303) ∨ (¬ p1096)) : (¬ p1095) ∨ (¬ p125) ∨ (¬ p425) ∨ p63 ∨ (¬ p665) ∨ (¬ p303) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p582 := by
    exact h35574
  rcases h27852 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step35857 (p48 p234 p305 p344 p422 p424 p425 p582 p1055 p1076 : Prop)
    (h35574 : p582)
    (h27853 : (¬ p425) ∨ (¬ p305) ∨ p422 ∨ (¬ p234) ∨ p1076 ∨ p344 ∨ (¬ p48) ∨ p424 ∨ (¬ p1055) ∨ (¬ p582)) : p424 ∨ (¬ p305) ∨ p422 ∨ (¬ p234) ∨ p1076 ∨ p344 ∨ (¬ p48) ∨ (¬ p425) ∨ (¬ p1055) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p582 := by
    exact h35574
  rcases h27853 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)
  · exact False.elim (u0 q7)
  · exact False.elim (q8 u8)
  · exact False.elim (q9 u9)

theorem step35878 (p2 p3 p12 p540 p668 : Prop)
    (h35527 : p668)
    (h20464 : (¬ p2) ∨ (¬ p3) ∨ (¬ p12) ∨ (¬ p540) ∨ (¬ p668)) : (¬ p540) ∨ (¬ p12) ∨ (¬ p3) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p540 := by
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
  have u3 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p668 := by
    exact h35527
  rcases h20464 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)

theorem step35879 (p12 p163 p424 p540 p668 : Prop)
    (h35527 : p668)
    (h27903 : p424 ∨ (¬ p540) ∨ (¬ p12) ∨ (¬ p163) ∨ (¬ p668)) : p424 ∨ (¬ p12) ∨ (¬ p540) ∨ (¬ p163) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p540 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p668 := by
    exact h35527
  rcases h27903 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)

theorem step35880 (p12 p14 p234 p543 p664 : Prop)
    (h35502 : p664)
    (h27910 : p14 ∨ p12 ∨ (¬ p234) ∨ (¬ p664) ∨ (¬ p543)) : (¬ p234) ∨ p14 ∨ p12 ∨ (¬ p543) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p14) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p543 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p664 := by
    exact h35502
  rcases h27910 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)

theorem step35884 (p17 p86 p161 p258 p533 p756 p1229 : Prop)
    (h35501 : p533)
    (h35496 : p86)
    (h27955 : (¬ p756) ∨ p1229 ∨ (¬ p533) ∨ p258 ∨ p17 ∨ (¬ p161) ∨ (¬ p86)) : p258 ∨ (¬ p756) ∨ p1229 ∨ p17 ∨ (¬ p161) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p258) := fun hu => hn (Or.inl hu)
  have u1 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p533 := by
    exact h35501
  have u6 : p86 := by
    exact h35496
  rcases h27955 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u5)
  · exact False.elim (u0 q3)
  · exact False.elim (u3 q4)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u6)

theorem step35887 (p39 p63 p68 p101 p121 p161 p211 p227 p1229 : Prop)
    (h35495 : p39)
    (h27960 : p121 ∨ (¬ p211) ∨ (¬ p227) ∨ p101 ∨ (¬ p63) ∨ (¬ p161) ∨ (¬ p68) ∨ p1229 ∨ (¬ p39)) : (¬ p227) ∨ p121 ∨ (¬ p211) ∨ p101 ∨ (¬ p63) ∨ (¬ p161) ∨ (¬ p68) ∨ p1229 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p121) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p211 := by
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
  have u7 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p39 := by
    exact h35495
  rcases h27960 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)
  · exact False.elim (u7 q7)
  · exact False.elim (q8 u8)

theorem step35889 (p124 p161 p344 p496 p728 p1229 p1330 : Prop)
    (h35500 : p496)
    (h27974 : (¬ p728) ∨ (¬ p344) ∨ (¬ p161) ∨ (¬ p1330) ∨ p1229 ∨ (¬ p496) ∨ (¬ p124)) : (¬ p344) ∨ (¬ p161) ∨ (¬ p728) ∨ (¬ p1330) ∨ p1229 ∨ (¬ p124) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p496 := by
    exact h35500
  rcases h27974 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u5)

theorem step35890 (p124 p161 p496 p1035 p1044 p1076 p1229 : Prop)
    (h35500 : p496)
    (h27975 : p1076 ∨ (¬ p124) ∨ (¬ p496) ∨ (¬ p1035) ∨ p1229 ∨ (¬ p161) ∨ (¬ p1044)) : p1076 ∨ (¬ p1035) ∨ (¬ p124) ∨ p1229 ∨ (¬ p161) ∨ (¬ p1044) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1076) := fun hu => hn (Or.inl hu)
  have u1 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1044 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p496 := by
    exact h35500
  rcases h27975 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (u3 q4)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step35891 (p11 p15 p39 p88 p261 p1035 p1145 p1229 p1624 p1651 : Prop)
    (h35495 : p39)
    (h27993 : (¬ p1651) ∨ (¬ p1624) ∨ (¬ p11) ∨ (¬ p261) ∨ (¬ p88) ∨ (¬ p1145) ∨ (¬ p39) ∨ (¬ p1035) ∨ (¬ p1229) ∨ p15) : (¬ p1651) ∨ (¬ p1624) ∨ (¬ p11) ∨ (¬ p261) ∨ (¬ p88) ∨ (¬ p1145) ∨ (¬ p1035) ∨ (¬ p1229) ∨ p15 := by
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
  have u6 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p39 := by
    exact h35495
  rcases h27993 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (u8 q9)

theorem step35892 (p18 p67 p124 p161 p207 p533 p756 p1140 p1145 : Prop)
    (h35501 : p533)
    (h27994 : (¬ p756) ∨ (¬ p124) ∨ (¬ p161) ∨ (¬ p533) ∨ (¬ p1145) ∨ (¬ p207) ∨ (¬ p67) ∨ p18 ∨ p1140) : (¬ p756) ∨ (¬ p124) ∨ (¬ p161) ∨ (¬ p1145) ∨ (¬ p207) ∨ (¬ p67) ∨ p18 ∨ p1140 := by
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
  have u3 : p1145 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p533 := by
    exact h35501
  rcases h27994 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (u6 q7)
  · exact False.elim (u7 q8)

theorem step35893 (p15 p39 p88 p185 p985 p1145 p1211 p1229 p1452 p1584 : Prop)
    (h35495 : p39)
    (h35503 : p985)
    (h27995 : (¬ p1211) ∨ (¬ p1452) ∨ (¬ p39) ∨ p15 ∨ (¬ p88) ∨ (¬ p185) ∨ (¬ p1584) ∨ (¬ p1229) ∨ (¬ p985) ∨ (¬ p1145)) : (¬ p1211) ∨ (¬ p1452) ∨ p15 ∨ (¬ p88) ∨ (¬ p185) ∨ (¬ p1584) ∨ (¬ p1229) ∨ (¬ p1145) := by
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
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1145 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p39 := by
    exact h35495
  have u9 : p985 := by
    exact h35503
  rcases h27995 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u8)
  · exact False.elim (u2 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u9)
  · exact False.elim (q9 u7)

theorem step35894 (p63 p124 p496 p533 p756 p1249 p1489 : Prop)
    (h35501 : p533)
    (h35500 : p496)
    (h28016 : (¬ p756) ∨ (¬ p124) ∨ p63 ∨ (¬ p533) ∨ (¬ p496) ∨ (¬ p1489) ∨ (¬ p1249)) : (¬ p756) ∨ p63 ∨ (¬ p124) ∨ (¬ p1489) ∨ (¬ p1249) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p63) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p533 := by
    exact h35501
  have u6 : p496 := by
    exact h35500
  rcases h28016 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)

theorem step35895 (p3 p63 p533 p534 p1249 p1489 : Prop)
    (h35501 : p533)
    (h28018 : (¬ p534) ∨ p63 ∨ (¬ p533) ∨ (¬ p1249) ∨ (¬ p3) ∨ (¬ p1489)) : (¬ p534) ∨ (¬ p1249) ∨ p63 ∨ (¬ p3) ∨ (¬ p1489) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p533 := by
    exact h35501
  rcases h28018 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step35896 (p63 p125 p434 p496 p1249 p1330 p1489 : Prop)
    (h35500 : p496)
    (h28019 : (¬ p434) ∨ (¬ p496) ∨ (¬ p1489) ∨ p125 ∨ (¬ p1249) ∨ p63 ∨ (¬ p1330)) : (¬ p434) ∨ p63 ∨ (¬ p1489) ∨ p125 ∨ (¬ p1249) ∨ (¬ p1330) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p63) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p496 := by
    exact h35500
  rcases h28019 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (u1 q5)
  · exact False.elim (q6 u5)

theorem step35897 (p11 p258 p344 p668 p1082 : Prop)
    (h35527 : p668)
    (h28033 : (¬ p258) ∨ p344 ∨ p11 ∨ (¬ p1082) ∨ (¬ p668)) : p11 ∨ (¬ p258) ∨ p344 ∨ (¬ p1082) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p11) := fun hu => hn (Or.inl hu)
  have u1 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1082 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p668 := by
    exact h35527
  rcases h28033 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (u2 q1)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)

theorem step35899 (p185 p668 p836 p1121 p1346 : Prop)
    (h35527 : p668)
    (h20188 : (¬ p185) ∨ (¬ p668) ∨ (¬ p836) ∨ (¬ p1121) ∨ (¬ p1346)) : (¬ p836) ∨ (¬ p185) ∨ (¬ p1346) ∨ (¬ p1121) := by
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
  have u2 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p668 := by
    exact h35527
  rcases h20188 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)

theorem step35901 (p8 p15 p234 p419 p431 p734 p1103 : Prop)
    (h35504 : p1103)
    (h28056 : (¬ p734) ∨ (¬ p431) ∨ p8 ∨ p419 ∨ (¬ p15) ∨ (¬ p1103) ∨ (¬ p234)) : (¬ p734) ∨ (¬ p15) ∨ p8 ∨ (¬ p431) ∨ p419 ∨ (¬ p234) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1103 := by
    exact h35504
  rcases h28056 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (u2 q2)
  · exact False.elim (u4 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u5)

theorem step35903 (p48 p156 p234 p424 p918 : Prop)
    (h35659 : p156)
    (h28060 : (¬ p156) ∨ p424 ∨ (¬ p48) ∨ (¬ p234) ∨ (¬ p918)) : p424 ∨ (¬ p234) ∨ (¬ p48) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p156 := by
    exact h35659
  rcases h28060 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)

theorem step35904 (p15 p234 p542 p836 p1055 p1103 p1115 : Prop)
    (h35504 : p1103)
    (h28061 : p1115 ∨ (¬ p836) ∨ (¬ p1055) ∨ (¬ p234) ∨ (¬ p542) ∨ (¬ p15) ∨ (¬ p1103)) : (¬ p836) ∨ (¬ p234) ∨ p1115 ∨ (¬ p1055) ∨ (¬ p542) ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1055 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1103 := by
    exact h35504
  rcases h28061 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)

theorem step35905 (p15 p63 p124 p234 p344 p425 p542 p582 : Prop)
    (h35574 : p582)
    (h28064 : (¬ p425) ∨ p124 ∨ (¬ p582) ∨ (¬ p542) ∨ (¬ p15) ∨ p63 ∨ p344 ∨ (¬ p234)) : p124 ∨ (¬ p542) ∨ (¬ p425) ∨ (¬ p15) ∨ p63 ∨ p344 ∨ (¬ p234) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p582 := by
    exact h35574
  rcases h28064 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)
  · exact False.elim (u4 q5)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u6)

theorem step35906 (p63 p86 p1249 p1346 : Prop)
    (h35496 : p86)
    (h28078 : (¬ p1346) ∨ (¬ p1249) ∨ p63 ∨ (¬ p86)) : (¬ p1249) ∨ p63 ∨ (¬ p1346) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p63) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p86 := by
    exact h35496
  rcases h28078 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)

theorem step35907 (p244 p918 p1055 p1118 p1249 : Prop)
    (h35498 : p244)
    (h28086 : (¬ p1118) ∨ p1055 ∨ (¬ p1249) ∨ p918 ∨ (¬ p244)) : (¬ p1118) ∨ (¬ p1249) ∨ p1055 ∨ p918 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1118 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p244 := by
    exact h35498
  rcases h28086 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)

theorem step35908 (p41 p195 p1140 p1249 p1253 : Prop)
    (h35556 : p195)
    (h18603 : (¬ p41) ∨ (¬ p195) ∨ (¬ p1140) ∨ (¬ p1249) ∨ (¬ p1253)) : (¬ p1140) ∨ (¬ p1253) ∨ (¬ p1249) ∨ (¬ p41) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1253 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p195 := by
    exact h35556
  rcases h18603 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u1)

theorem step35910 (p41 p83 p125 p189 p303 p496 p864 p1249 : Prop)
    (h35500 : p496)
    (h28089 : (¬ p864) ∨ (¬ p1249) ∨ (¬ p496) ∨ (¬ p189) ∨ (¬ p83) ∨ (¬ p41) ∨ p303 ∨ p125) : (¬ p864) ∨ (¬ p1249) ∨ (¬ p189) ∨ (¬ p83) ∨ (¬ p41) ∨ p303 ∨ p125 := by
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
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p496 := by
    exact h35500
  rcases h28089 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)
  · exact False.elim (u6 q7)

theorem step35911 (p6 p10 p39 p68 p434 p1249 p1330 p1489 : Prop)
    (h35495 : p39)
    (h28094 : (¬ p434) ∨ (¬ p1489) ∨ (¬ p39) ∨ (¬ p68) ∨ (¬ p1330) ∨ (¬ p1249) ∨ p10 ∨ p6) : (¬ p1249) ∨ (¬ p434) ∨ (¬ p68) ∨ (¬ p1330) ∨ (¬ p1489) ∨ p10 ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p39 := by
    exact h35495
  rcases h28094 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u0)
  · exact False.elim (u5 q6)
  · exact False.elim (u6 q7)

theorem step35912 (p595 p635 p664 p902 p1076 p1096 : Prop)
    (h35502 : p664)
    (h28108 : (¬ p635) ∨ p1096 ∨ (¬ p902) ∨ (¬ p1076) ∨ (¬ p595) ∨ (¬ p664)) : (¬ p902) ∨ (¬ p595) ∨ (¬ p635) ∨ (¬ p1076) ∨ p1096 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p902 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p635 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p664 := by
    exact h35502
  rcases h28108 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u5)

theorem step35913 (p5 p6 p101 p664 p897 p1076 p1096 : Prop)
    (h35502 : p664)
    (h28141 : (¬ p101) ∨ (¬ p1076) ∨ p897 ∨ (¬ p6) ∨ (¬ p1096) ∨ (¬ p664) ∨ (¬ p5)) : (¬ p1096) ∨ (¬ p5) ∨ p897 ∨ (¬ p6) ∨ (¬ p101) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p664 := by
    exact h35502
  rcases h28141 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u1)

theorem step35914 (p156 p189 p728 p897 p923 p1330 p1349 p1489 : Prop)
    (h35659 : p156)
    (h28142 : p897 ∨ (¬ p1349) ∨ (¬ p156) ∨ (¬ p1489) ∨ (¬ p1330) ∨ (¬ p923) ∨ (¬ p728) ∨ p189) : p897 ∨ (¬ p1349) ∨ (¬ p1489) ∨ (¬ p1330) ∨ (¬ p923) ∨ (¬ p728) ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p897) := fun hu => hn (Or.inl hu)
  have u1 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p923 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p156 := by
    exact h35659
  rcases h28142 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (u6 q7)

theorem step35916 (p11 p16 p17 p224 p389 p897 p1096 : Prop)
    (h35539 : p16)
    (h28148 : (¬ p11) ∨ (¬ p389) ∨ p897 ∨ (¬ p16) ∨ p224 ∨ (¬ p17) ∨ (¬ p1096)) : (¬ p389) ∨ (¬ p1096) ∨ p897 ∨ p224 ∨ (¬ p17) ∨ (¬ p11) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p16 := by
    exact h35539
  rcases h28148 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u0)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (u3 q4)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u1)

theorem step35917 (p16 p134 p188 p224 p422 p897 p1096 p1140 : Prop)
    (h35539 : p16)
    (h28153 : p1140 ∨ p897 ∨ (¬ p16) ∨ (¬ p1096) ∨ (¬ p188) ∨ p224 ∨ (¬ p134) ∨ p422) : p897 ∨ p1140 ∨ (¬ p1096) ∨ (¬ p188) ∨ p224 ∨ (¬ p134) ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p897) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1140) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p16 := by
    exact h35539
  rcases h28153 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u4 q5)
  · exact False.elim (q6 u5)
  · exact False.elim (u6 q7)

theorem step35919 (p15 p39 p88 p303 p351 p382 p815 p897 p1096 : Prop)
    (h35495 : p39)
    (h28157 : (¬ p1096) ∨ p897 ∨ (¬ p815) ∨ (¬ p88) ∨ (¬ p351) ∨ p303 ∨ (¬ p382) ∨ (¬ p39) ∨ p15) : p897 ∨ (¬ p1096) ∨ (¬ p815) ∨ (¬ p88) ∨ (¬ p351) ∨ p303 ∨ (¬ p382) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p897) := fun hu => hn (Or.inl hu)
  have u1 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
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
  have u7 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p39 := by
    exact h35495
  rcases h28157 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u8)
  · exact False.elim (u7 q8)

theorem step35920 (p15 p39 p88 p185 p664 p897 p1096 p1115 : Prop)
    (h35495 : p39)
    (h35502 : p664)
    (h28159 : (¬ p1115) ∨ p897 ∨ p15 ∨ (¬ p39) ∨ (¬ p185) ∨ (¬ p88) ∨ (¬ p1096) ∨ (¬ p664)) : (¬ p1115) ∨ p897 ∨ p15 ∨ (¬ p185) ∨ (¬ p88) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p897) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p39 := by
    exact h35495
  have u7 : p664 := by
    exact h35502
  rcases h28159 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u7)

theorem step35928 (p8 p15 p16 p18 p101 p238 p836 p1115 : Prop)
    (h35539 : p16)
    (h28174 : (¬ p1115) ∨ (¬ p15) ∨ p8 ∨ p101 ∨ p836 ∨ p18 ∨ (¬ p16) ∨ (¬ p238)) : (¬ p1115) ∨ (¬ p238) ∨ p8 ∨ p101 ∨ p836 ∨ (¬ p15) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p16 := by
    exact h35539
  rcases h28174 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (u2 q2)
  · exact False.elim (u3 q3)
  · exact False.elim (u4 q4)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u1)

theorem step35930 (p156 p189 p238 p1055 p1115 : Prop)
    (h35659 : p156)
    (h28179 : (¬ p1055) ∨ p1115 ∨ (¬ p238) ∨ p189 ∨ (¬ p156)) : (¬ p1055) ∨ (¬ p238) ∨ p1115 ∨ p189 := by
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
  have u2 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p156 := by
    exact h35659
  rcases h28179 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)

theorem step35931 (p8 p156 p189 p238 p836 : Prop)
    (h35659 : p156)
    (h28180 : p8 ∨ p189 ∨ (¬ p156) ∨ (¬ p238) ∨ p836) : (¬ p238) ∨ p189 ∨ p8 ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p156 := by
    exact h35659
  rcases h28180 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (u3 q4)

theorem step35933 (p8 p15 p24 p39 p88 p101 p238 p290 p495 p836 : Prop)
    (h35495 : p39)
    (h28183 : (¬ p290) ∨ p15 ∨ (¬ p24) ∨ (¬ p238) ∨ p836 ∨ (¬ p88) ∨ p495 ∨ (¬ p39) ∨ p101 ∨ p8) : (¬ p290) ∨ (¬ p238) ∨ (¬ p24) ∨ p15 ∨ p836 ∨ (¬ p88) ∨ p495 ∨ p101 ∨ p8 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p290 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p39 := by
    exact h35495
  rcases h28183 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)
  · exact False.elim (q7 u9)
  · exact False.elim (u7 q8)
  · exact False.elim (u8 q9)

theorem step35934 (p6 p10 p190 p238 p347 p836 p1055 p1115 : Prop)
    (h35646 : p347)
    (h28184 : p1115 ∨ (¬ p836) ∨ (¬ p238) ∨ p10 ∨ (¬ p190) ∨ (¬ p1055) ∨ p6 ∨ (¬ p347)) : p10 ∨ (¬ p836) ∨ p1115 ∨ (¬ p238) ∨ (¬ p190) ∨ (¬ p1055) ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p10) := fun hu => hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p347 := by
    exact h35646
  rcases h28184 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)
  · exact False.elim (q7 u7)

theorem step35935 (p87 p238 p918 p1055 p1115 : Prop)
    (h35497 : p87)
    (h28190 : p918 ∨ (¬ p1055) ∨ (¬ p238) ∨ p1115 ∨ (¬ p87)) : (¬ p1055) ∨ p918 ∨ (¬ p238) ∨ p1115 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p87 := by
    exact h35497
  rcases h28190 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)

theorem step35936 (p6 p8 p39 p68 p88 p121 p238 p836 p1081 p1115 : Prop)
    (h35495 : p39)
    (h28191 : (¬ p1115) ∨ (¬ p68) ∨ p8 ∨ p836 ∨ (¬ p121) ∨ (¬ p1081) ∨ p6 ∨ (¬ p238) ∨ (¬ p88) ∨ (¬ p39)) : (¬ p1115) ∨ (¬ p121) ∨ p8 ∨ p836 ∨ (¬ p68) ∨ (¬ p1081) ∨ p6 ∨ (¬ p238) ∨ (¬ p88) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p68 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p39 := by
    exact h35495
  rcases h28191 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (u2 q2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u8)
  · exact False.elim (q9 u9)

theorem step35937 (p15 p39 p88 p344 p639 p789 p790 p1096 p1325 : Prop)
    (h35495 : p39)
    (h28228 : (¬ p344) ∨ p15 ∨ (¬ p639) ∨ (¬ p1096) ∨ (¬ p88) ∨ (¬ p1325) ∨ p790 ∨ (¬ p39) ∨ p789) : (¬ p344) ∨ (¬ p639) ∨ p15 ∨ (¬ p1096) ∨ (¬ p88) ∨ (¬ p1325) ∨ p790 ∨ p789 := by
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
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
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
  have u7 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p39 := by
    exact h35495
  rcases h28228 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)
  · exact False.elim (q7 u8)
  · exact False.elim (u7 q8)

theorem step35939 (p126 p258 p348 p664 p1076 : Prop)
    (h35502 : p664)
    (h16414 : (¬ p126) ∨ (¬ p258) ∨ (¬ p348) ∨ (¬ p664) ∨ (¬ p1076)) : (¬ p348) ∨ (¬ p258) ∨ (¬ p1076) ∨ (¬ p126) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p348 := by
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
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p664 := by
    exact h35502
  rcases h16414 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u2)

theorem step35940 (p1 p12 p664 p734 p1366 : Prop)
    (h35502 : p664)
    (h28249 : (¬ p1366) ∨ (¬ p1) ∨ (¬ p734) ∨ p12 ∨ (¬ p664)) : (¬ p734) ∨ (¬ p1366) ∨ (¬ p1) ∨ p12 := by
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
  have u2 : p1 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p664 := by
    exact h35502
  rcases h28249 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)

theorem step35946 (p2 p156 p185 p192 p303 p419 p517 p790 : Prop)
    (h35659 : p156)
    (h28285 : (¬ p517) ∨ (¬ p2) ∨ p303 ∨ (¬ p185) ∨ (¬ p419) ∨ (¬ p192) ∨ (¬ p790) ∨ (¬ p156)) : (¬ p517) ∨ p303 ∨ (¬ p2) ∨ (¬ p185) ∨ (¬ p419) ∨ (¬ p192) ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p517 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p156 := by
    exact h35659
  rcases h28285 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u7)

theorem step35957 (p125 p420 p455 p498 p980 p1056 p1081 p1103 p1226 : Prop)
    (h35504 : p1103)
    (h28311 : (¬ p420) ∨ (¬ p498) ∨ (¬ p455) ∨ (¬ p1226) ∨ (¬ p1056) ∨ p980 ∨ (¬ p1103) ∨ (¬ p1081) ∨ p125) : (¬ p1226) ∨ (¬ p420) ∨ (¬ p455) ∨ (¬ p498) ∨ (¬ p1056) ∨ p980 ∨ (¬ p1081) ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1226 := by
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
  have u4 : p1056 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1103 := by
    exact h35504
  rcases h28311 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u6)
  · exact False.elim (u7 q8)

theorem step35958 (p86 p189 p303 p420 p422 p495 p1000 : Prop)
    (h35496 : p86)
    (h28315 : (¬ p420) ∨ p422 ∨ (¬ p495) ∨ (¬ p303) ∨ (¬ p86) ∨ p189 ∨ (¬ p1000)) : (¬ p420) ∨ p422 ∨ (¬ p495) ∨ (¬ p303) ∨ p189 ∨ (¬ p1000) := by
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
  have u4 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p86 := by
    exact h35496
  rcases h28315 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (u4 q5)
  · exact False.elim (q6 u5)

theorem step35959 (p327 p382 p419 p420 p455 p494 p617 p961 : Prop)
    (h35549 : p327)
    (h28320 : p382 ∨ (¬ p420) ∨ (¬ p617) ∨ (¬ p961) ∨ (¬ p419) ∨ (¬ p327) ∨ (¬ p494) ∨ (¬ p455)) : p382 ∨ (¬ p420) ∨ (¬ p617) ∨ (¬ p961) ∨ (¬ p419) ∨ (¬ p494) ∨ (¬ p455) := by
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
  have u5 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p327 := by
    exact h35549
  rcases h28320 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step35960 (p83 p1233 p1350 : Prop)
    (h35505 : p1233)
    (h14243 : (¬ p83) ∨ (¬ p1233) ∨ p1350) : p1350 ∨ (¬ p83) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1350) := fun hu => hn (Or.inl hu)
  have u1 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p1233 := by
    exact h35505
  rcases h14243 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (u0 q2)

theorem step35967 (p17 p86 p126 p434 p595 p1287 : Prop)
    (h35496 : p86)
    (h28409 : (¬ p434) ∨ p17 ∨ (¬ p126) ∨ (¬ p1287) ∨ (¬ p86) ∨ p595) : (¬ p126) ∨ (¬ p434) ∨ p17 ∨ (¬ p1287) ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p86 := by
    exact h35496
  rcases h28409 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)
  · exact False.elim (u4 q5)

theorem step35968 (p17 p86 p126 p303 p431 p595 p1545 : Prop)
    (h35496 : p86)
    (h28413 : p303 ∨ (¬ p431) ∨ (¬ p86) ∨ p595 ∨ (¬ p1545) ∨ (¬ p126) ∨ p17) : p303 ∨ p595 ∨ (¬ p431) ∨ (¬ p1545) ∨ (¬ p126) ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p595) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p86 := by
    exact h35496
  rcases h28413 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)

theorem step35969 (p18 p39 p63 p121 p228 p595 p1287 : Prop)
    (h35495 : p39)
    (h28415 : p18 ∨ p595 ∨ (¬ p63) ∨ (¬ p1287) ∨ (¬ p121) ∨ (¬ p39) ∨ (¬ p228)) : (¬ p1287) ∨ p595 ∨ (¬ p63) ∨ p18 ∨ (¬ p121) ∨ (¬ p228) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p595) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p39 := by
    exact h35495
  rcases h28415 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u5)

theorem step35970 (p8 p39 p63 p68 p561 p595 p728 p789 p1388 : Prop)
    (h35495 : p39)
    (h28429 : p595 ∨ (¬ p561) ∨ (¬ p1388) ∨ (¬ p63) ∨ p789 ∨ (¬ p68) ∨ (¬ p728) ∨ (¬ p8) ∨ (¬ p39)) : (¬ p1388) ∨ (¬ p561) ∨ p595 ∨ (¬ p63) ∨ p789 ∨ (¬ p68) ∨ (¬ p728) ∨ (¬ p8) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1388 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p39 := by
    exact h35495
  rcases h28429 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u8)

theorem step35971 (p39 p63 p68 p561 p595 p980 p1015 p1055 p1335 p1388 : Prop)
    (h35495 : p39)
    (h28430 : p980 ∨ p1055 ∨ p595 ∨ (¬ p1388) ∨ (¬ p561) ∨ (¬ p39) ∨ (¬ p68) ∨ (¬ p1015) ∨ (¬ p1335) ∨ (¬ p63)) : p1055 ∨ p595 ∨ p980 ∨ (¬ p1388) ∨ (¬ p561) ∨ (¬ p68) ∨ (¬ p1015) ∨ (¬ p1335) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1055) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p595) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1388 := by
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
  have u6 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p39 := by
    exact h35495
  rcases h28430 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step35972 (p2 p3 p14 p303 p327 p595 p1287 : Prop)
    (h35549 : p327)
    (h28432 : p303 ∨ p3 ∨ (¬ p327) ∨ p2 ∨ (¬ p14) ∨ (¬ p1287) ∨ p595) : p303 ∨ p2 ∨ p3 ∨ (¬ p14) ∨ (¬ p1287) ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p2) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p327 := by
    exact h35549
  rcases h28432 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)

theorem step35975 (p39 p63 p68 p101 p121 p211 p227 p642 p1096 : Prop)
    (h35495 : p39)
    (h28449 : p121 ∨ (¬ p227) ∨ (¬ p68) ∨ (¬ p211) ∨ (¬ p63) ∨ (¬ p39) ∨ (¬ p642) ∨ p1096 ∨ p101) : (¬ p227) ∨ (¬ p68) ∨ p121 ∨ (¬ p211) ∨ (¬ p63) ∨ (¬ p642) ∨ p1096 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p121) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p642 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p39 := by
    exact h35495
  rcases h28449 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u5)
  · exact False.elim (u6 q7)
  · exact False.elim (u7 q8)

theorem step35976 (p11 p17 p86 p985 p1096 p1452 p1538 : Prop)
    (h35496 : p86)
    (h35503 : p985)
    (h28455 : (¬ p1538) ∨ (¬ p1452) ∨ p17 ∨ p1096 ∨ (¬ p86) ∨ p11 ∨ (¬ p985)) : (¬ p1538) ∨ (¬ p1452) ∨ p17 ∨ p1096 ∨ p11 := by
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
  have u4 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p86 := by
    exact h35496
  have u6 : p985 := by
    exact h35503
  rcases h28455 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u2 q2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u5)
  · exact False.elim (u4 q5)
  · exact False.elim (q6 u6)

theorem step35977 (p86 p789 p790 p985 p1096 p1325 p1538 : Prop)
    (h35503 : p985)
    (h35496 : p86)
    (h28456 : (¬ p1538) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p985) ∨ p1325 ∨ (¬ p86) ∨ p1096) : (¬ p1538) ∨ p1096 ∨ (¬ p790) ∨ p1325 ∨ (¬ p789) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1538 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p985 := by
    exact h35503
  have u6 : p86 := by
    exact h35496
  rcases h28456 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (u3 q4)
  · exact False.elim (q5 u6)
  · exact False.elim (u1 q6)

theorem step35978 (p15 p17 p49 p84 p126 p347 p897 p1096 : Prop)
    (h35646 : p347)
    (h28464 : (¬ p347) ∨ (¬ p84) ∨ (¬ p15) ∨ (¬ p126) ∨ (¬ p897) ∨ p17 ∨ p1096 ∨ (¬ p49)) : p17 ∨ p1096 ∨ (¬ p15) ∨ (¬ p126) ∨ (¬ p897) ∨ (¬ p84) ∨ (¬ p49) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p17) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
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
  have u5 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p347 := by
    exact h35646
  rcases h28464 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (u0 q5)
  · exact False.elim (u1 q6)
  · exact False.elim (q7 u6)

theorem step35979 (p86 p189 p224 p422 p897 p1000 p1096 : Prop)
    (h35496 : p86)
    (h28465 : p422 ∨ p189 ∨ (¬ p224) ∨ (¬ p1000) ∨ (¬ p86) ∨ (¬ p897) ∨ p1096) : (¬ p224) ∨ p422 ∨ p189 ∨ (¬ p1000) ∨ (¬ p897) ∨ p1096 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p422) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p86 := by
    exact h35496
  rcases h28465 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)

theorem step35981 (p15 p49 p84 p185 p668 p897 p1096 p1115 : Prop)
    (h35527 : p668)
    (h28469 : (¬ p84) ∨ p1096 ∨ (¬ p15) ∨ (¬ p668) ∨ p185 ∨ p1115 ∨ (¬ p49) ∨ (¬ p897)) : (¬ p84) ∨ (¬ p15) ∨ p1096 ∨ p185 ∨ p1115 ∨ (¬ p49) ∨ (¬ p897) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p668 := by
    exact h35527
  rcases h28469 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u7)
  · exact False.elim (u3 q4)
  · exact False.elim (u4 q5)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step35982 (p125 p348 p496 p897 p1096 : Prop)
    (h35500 : p496)
    (h28472 : (¬ p348) ∨ p1096 ∨ (¬ p897) ∨ p125 ∨ (¬ p496)) : (¬ p348) ∨ p1096 ∨ (¬ p897) ∨ p125 := by
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
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p496 := by
    exact h35500
  rcases h28472 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)

theorem step35983 (p41 p63 p156 p923 p1096 : Prop)
    (h35659 : p156)
    (h28474 : (¬ p41) ∨ p1096 ∨ (¬ p63) ∨ (¬ p923) ∨ (¬ p156)) : (¬ p63) ∨ p1096 ∨ (¬ p41) ∨ (¬ p923) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p923 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p156 := by
    exact h35659
  rcases h28474 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)

theorem step35984 (p125 p434 p496 p980 p1074 p1096 p1330 : Prop)
    (h35500 : p496)
    (h28475 : (¬ p434) ∨ p1096 ∨ (¬ p1074) ∨ (¬ p1330) ∨ (¬ p496) ∨ (¬ p980) ∨ p125) : (¬ p434) ∨ p1096 ∨ (¬ p1074) ∨ (¬ p1330) ∨ (¬ p980) ∨ p125 := by
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
  have u4 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p496 := by
    exact h35500
  rcases h28475 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)

theorem step35985 (p48 p124 p344 p424 p425 p542 p582 p1711 p1712 : Prop)
    (h35574 : p582)
    (h28478 : (¬ p1712) ∨ (¬ p1711) ∨ (¬ p542) ∨ p124 ∨ p344 ∨ (¬ p425) ∨ (¬ p424) ∨ (¬ p582) ∨ (¬ p48)) : (¬ p1711) ∨ (¬ p1712) ∨ (¬ p542) ∨ p124 ∨ p344 ∨ (¬ p425) ∨ (¬ p424) ∨ (¬ p48) := by
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
  have u7 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p582 := by
    exact h35574
  rcases h28478 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u7)

theorem step35988 (p2 p48 p68 p134 p344 p424 p495 p582 p635 p1096 : Prop)
    (h35574 : p582)
    (h28481 : p424 ∨ p344 ∨ p495 ∨ p2 ∨ (¬ p582) ∨ p134 ∨ (¬ p635) ∨ (¬ p48) ∨ p1096 ∨ (¬ p68)) : p424 ∨ p495 ∨ p344 ∨ p2 ∨ p134 ∨ (¬ p635) ∨ (¬ p48) ∨ p1096 ∨ (¬ p68) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p635 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p582 := by
    exact h35574
  rcases h28481 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u9)
  · exact False.elim (u4 q5)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (u7 q8)
  · exact False.elim (q9 u8)

theorem step35989 (p3 p48 p68 p125 p163 p303 p422 p425 p582 p1000 : Prop)
    (h35574 : p582)
    (h28482 : (¬ p425) ∨ p163 ∨ (¬ p582) ∨ (¬ p125) ∨ (¬ p303) ∨ (¬ p1000) ∨ (¬ p48) ∨ (¬ p3) ∨ (¬ p68) ∨ p422) : p163 ∨ (¬ p125) ∨ (¬ p425) ∨ (¬ p303) ∨ (¬ p1000) ∨ (¬ p48) ∨ (¬ p3) ∨ (¬ p68) ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p163) := fun hu => hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p48 := by
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
  have u8 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p582 := by
    exact h35574
  rcases h28482 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u2)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (u8 q9)

theorem step35991 (p14 p48 p87 p163 p189 : Prop)
    (h35497 : p87)
    (h28484 : (¬ p48) ∨ p163 ∨ (¬ p189) ∨ (¬ p14) ∨ (¬ p87)) : p163 ∨ (¬ p189) ∨ (¬ p48) ∨ (¬ p14) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p163) := fun hu => hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p87 := by
    exact h35497
  rcases h28484 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)

theorem step35992 (p2 p48 p64 p234 p495 p582 : Prop)
    (h35574 : p582)
    (h28485 : (¬ p2) ∨ p495 ∨ (¬ p48) ∨ (¬ p64) ∨ (¬ p582) ∨ (¬ p234)) : (¬ p2) ∨ p495 ∨ (¬ p48) ∨ (¬ p64) ∨ (¬ p234) := by
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
  have u4 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p582 := by
    exact h35574
  rcases h28485 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u4)

theorem step35994 (p3 p14 p17 p64 p86 p234 p258 p325 : Prop)
    (h35496 : p86)
    (h28490 : (¬ p325) ∨ p17 ∨ p3 ∨ (¬ p64) ∨ p258 ∨ (¬ p86) ∨ p234 ∨ (¬ p14)) : (¬ p325) ∨ p17 ∨ p3 ∨ (¬ p64) ∨ p258 ∨ p234 ∨ (¬ p14) := by
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
  have u5 : (¬ p234) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p86 := by
    exact h35496
  rcases h28490 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u7)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u6)

theorem step35996 (p2 p39 p63 p64 p234 : Prop)
    (h35495 : p39)
    (h20442 : (¬ p2) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p64) ∨ (¬ p234)) : (¬ p234) ∨ (¬ p63) ∨ (¬ p2) ∨ (¬ p64) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p39 := by
    exact h35495
  rcases h20442 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u0)

theorem step35998 (p2 p14 p17 p64 p86 p110 p234 p258 : Prop)
    (h35496 : p86)
    (h28495 : (¬ p2) ∨ p17 ∨ (¬ p64) ∨ (¬ p234) ∨ (¬ p110) ∨ p258 ∨ p14 ∨ (¬ p86)) : (¬ p234) ∨ p17 ∨ (¬ p64) ∨ (¬ p2) ∨ (¬ p110) ∨ p258 ∨ p14 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p86 := by
    exact h35496
  rcases h28495 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u3)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)
  · exact False.elim (u5 q5)
  · exact False.elim (u6 q6)
  · exact False.elim (q7 u7)

theorem step36000 (p2 p4 p12 p14 p38 p325 p668 : Prop)
    (h35527 : p668)
    (h20378 : (¬ p2) ∨ (¬ p4) ∨ (¬ p12) ∨ (¬ p14) ∨ (¬ p38) ∨ (¬ p325) ∨ (¬ p668)) : (¬ p325) ∨ (¬ p12) ∨ (¬ p38) ∨ (¬ p4) ∨ (¬ p14) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p668 := by
    exact h35527
  rcases h20378 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u6)

theorem step36002 (p63 p126 p224 p347 p382 p495 p579 p709 p929 p1102 : Prop)
    (h35646 : p347)
    (h28547 : (¬ p579) ∨ (¬ p347) ∨ p495 ∨ (¬ p382) ∨ (¬ p1102) ∨ p63 ∨ p224 ∨ (¬ p709) ∨ (¬ p929) ∨ (¬ p126)) : (¬ p579) ∨ (¬ p709) ∨ p495 ∨ (¬ p382) ∨ (¬ p1102) ∨ p63 ∨ p224 ∨ (¬ p929) ∨ (¬ p126) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p579 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p709 := by
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
  have u7 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p347 := by
    exact h35646
  rcases h28547 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u9)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (u5 q5)
  · exact False.elim (u6 q6)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step36003 (p10 p134 p189 p224 p347 p382 p821 : Prop)
    (h35646 : p347)
    (h28557 : (¬ p347) ∨ p189 ∨ p10 ∨ (¬ p382) ∨ (¬ p821) ∨ p224 ∨ p134) : p10 ∨ (¬ p382) ∨ p189 ∨ (¬ p821) ∨ p224 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p10) := fun hu => hn (Or.inl hu)
  have u1 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p821 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p347 := by
    exact h35646
  rcases h28557 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (u2 q1)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)
  · exact False.elim (u4 q5)
  · exact False.elim (u5 q6)

theorem step36006 (p2 p84 p134 p186 p424 p495 p582 p595 p1287 : Prop)
    (h35574 : p582)
    (h28564 : p424 ∨ p495 ∨ (¬ p582) ∨ (¬ p1287) ∨ p134 ∨ p2 ∨ (¬ p186) ∨ p595 ∨ (¬ p84)) : p424 ∨ (¬ p1287) ∨ p495 ∨ p134 ∨ p2 ∨ (¬ p186) ∨ p595 ∨ (¬ p84) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p582 := by
    exact h35574
  rcases h28564 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u1)
  · exact False.elim (u3 q4)
  · exact False.elim (u4 q5)
  · exact False.elim (q6 u5)
  · exact False.elim (u6 q7)
  · exact False.elim (q8 u7)

theorem step36007 (p2 p86 p134 p186 p303 p420 p424 p495 : Prop)
    (h35496 : p86)
    (h28565 : p424 ∨ (¬ p186) ∨ (¬ p495) ∨ p134 ∨ (¬ p303) ∨ (¬ p86) ∨ p2 ∨ (¬ p420)) : p424 ∨ (¬ p186) ∨ (¬ p495) ∨ p134 ∨ (¬ p303) ∨ p2 ∨ (¬ p420) := by
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
  have u5 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p86 := by
    exact h35496
  rcases h28565 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u7)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u6)

theorem step36008 (p10 p86 p134 p189 p595 p1287 p1325 : Prop)
    (h35496 : p86)
    (h28576 : p189 ∨ p595 ∨ (¬ p1287) ∨ p134 ∨ (¬ p86) ∨ p10 ∨ (¬ p1325)) : (¬ p1287) ∨ p595 ∨ p189 ∨ p134 ∨ p10 ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p595) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p86 := by
    exact h35496
  rcases h28576 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u6)
  · exact False.elim (u4 q5)
  · exact False.elim (q6 u5)

theorem step36010 (p86 p134 p161 p189 p1229 p1449 p1665 : Prop)
    (h35496 : p86)
    (h28578 : (¬ p1665) ∨ p189 ∨ (¬ p161) ∨ (¬ p1449) ∨ p134 ∨ (¬ p86) ∨ p1229) : (¬ p1665) ∨ (¬ p161) ∨ p189 ∨ (¬ p1449) ∨ p134 ∨ p1229 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1449 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p86 := by
    exact h35496
  rcases h28578 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u6)
  · exact False.elim (u5 q6)

theorem step36011 (p10 p86 p134 p189 p382 p603 p614 p1286 : Prop)
    (h35496 : p86)
    (h28596 : (¬ p1286) ∨ p189 ∨ p134 ∨ (¬ p614) ∨ p10 ∨ (¬ p86) ∨ (¬ p382) ∨ (¬ p603)) : p134 ∨ p189 ∨ (¬ p1286) ∨ (¬ p614) ∨ p10 ∨ (¬ p382) ∨ (¬ p603) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p134) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p614 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p603 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p86 := by
    exact h35496
  rcases h28596 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (u1 q1)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step36012 (p3 p124 p134 p191 p207 p225 p668 p1076 : Prop)
    (h35527 : p668)
    (h28609 : p3 ∨ p1076 ∨ (¬ p191) ∨ (¬ p124) ∨ p134 ∨ (¬ p668) ∨ (¬ p225) ∨ (¬ p207)) : (¬ p191) ∨ p3 ∨ p1076 ∨ (¬ p124) ∨ p134 ∨ (¬ p225) ∨ (¬ p207) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p668 := by
    exact h35527
  rcases h28609 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step36014 (p2 p84 p134 p186 p424 p495 p582 p595 p1545 : Prop)
    (h35574 : p582)
    (h28630 : p495 ∨ p424 ∨ p595 ∨ p134 ∨ p2 ∨ (¬ p1545) ∨ (¬ p186) ∨ (¬ p84) ∨ (¬ p582)) : p424 ∨ p595 ∨ p495 ∨ p134 ∨ p2 ∨ (¬ p1545) ∨ (¬ p186) ∨ (¬ p84) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p595) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p582 := by
    exact h35574
  rcases h28630 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (u3 q3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u8)

theorem step36016 (p6 p16 p134 p188 p422 p595 p1004 p1286 : Prop)
    (h35539 : p16)
    (h28642 : (¬ p422) ∨ (¬ p1004) ∨ p134 ∨ (¬ p6) ∨ (¬ p16) ∨ (¬ p188) ∨ (¬ p1286) ∨ (¬ p595)) : (¬ p422) ∨ p134 ∨ (¬ p1004) ∨ (¬ p6) ∨ (¬ p188) ∨ (¬ p1286) ∨ (¬ p595) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p134) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p16 := by
    exact h35539
  rcases h28642 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step36017 (p6 p41 p87 p134 p188 : Prop)
    (h35497 : p87)
    (h28658 : (¬ p41) ∨ (¬ p188) ∨ p134 ∨ (¬ p6) ∨ (¬ p87)) : p134 ∨ (¬ p6) ∨ (¬ p41) ∨ (¬ p188) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p134) := fun hu => hn (Or.inl hu)
  have u1 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p87 := by
    exact h35497
  rcases h28658 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)

theorem step36020 (p86 p101 p134 p189 p224 p897 p1096 : Prop)
    (h35496 : p86)
    (h28674 : p1096 ∨ p189 ∨ (¬ p897) ∨ (¬ p86) ∨ (¬ p224) ∨ p134 ∨ p101) : p1096 ∨ p189 ∨ (¬ p897) ∨ (¬ p224) ∨ p134 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1096) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p86 := by
    exact h35496
  rcases h28674 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (u4 q5)
  · exact False.elim (u5 q6)

theorem step36021 (p15 p84 p134 p189 p495 p582 p1689 p1710 : Prop)
    (h35574 : p582)
    (h28675 : (¬ p1710) ∨ (¬ p1689) ∨ (¬ p84) ∨ p189 ∨ p495 ∨ (¬ p582) ∨ p15 ∨ p134) : (¬ p1689) ∨ (¬ p1710) ∨ (¬ p84) ∨ p189 ∨ p495 ∨ p15 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1689 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p582 := by
    exact h35574
  rcases h28675 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u7)
  · exact False.elim (u5 q6)
  · exact False.elim (u6 q7)

theorem step36022 (p48 p125 p134 p303 p425 p582 p1325 p1711 p1712 : Prop)
    (h35574 : p582)
    (h28677 : (¬ p1711) ∨ (¬ p1712) ∨ (¬ p1325) ∨ (¬ p125) ∨ (¬ p425) ∨ (¬ p48) ∨ (¬ p582) ∨ p134 ∨ (¬ p303)) : (¬ p1711) ∨ (¬ p1712) ∨ (¬ p1325) ∨ (¬ p125) ∨ (¬ p425) ∨ (¬ p48) ∨ p134 ∨ (¬ p303) := by
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
  have u6 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p582 := by
    exact h35574
  rcases h28677 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u8)
  · exact False.elim (u6 q7)
  · exact False.elim (q8 u7)

theorem step36023 (p10 p134 p171 p185 p224 p347 p382 p815 : Prop)
    (h35646 : p347)
    (h28701 : (¬ p171) ∨ p185 ∨ p224 ∨ p134 ∨ (¬ p815) ∨ (¬ p382) ∨ p10 ∨ (¬ p347)) : (¬ p171) ∨ p185 ∨ p224 ∨ p134 ∨ (¬ p815) ∨ (¬ p382) ∨ p10 := by
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
  have u6 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p347 := by
    exact h35646
  rcases h28701 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (u2 q2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)
  · exact False.elim (q7 u7)

theorem step36024 (p12 p107 p124 p125 p348 p664 : Prop)
    (h35502 : p664)
    (h28710 : p124 ∨ (¬ p348) ∨ (¬ p664) ∨ p125 ∨ p12 ∨ (¬ p107)) : p125 ∨ (¬ p348) ∨ p124 ∨ p12 ∨ (¬ p107) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p125) := fun hu => hn (Or.inl hu)
  have u1 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p107 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p664 := by
    exact h35502
  rcases h28710 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (u0 q3)
  · exact False.elim (u3 q4)
  · exact False.elim (q5 u4)

theorem step36025 (p16 p71 p101 p124 p211 p1349 p1449 p1489 p1665 : Prop)
    (h35539 : p16)
    (h17832 : (¬ p16) ∨ (¬ p71) ∨ (¬ p101) ∨ (¬ p124) ∨ (¬ p211) ∨ (¬ p1349) ∨ (¬ p1449) ∨ (¬ p1489) ∨ (¬ p1665)) : (¬ p1665) ∨ (¬ p1489) ∨ (¬ p1449) ∨ (¬ p101) ∨ (¬ p1349) ∨ (¬ p211) ∨ (¬ p71) ∨ (¬ p124) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1449 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p16 := by
    exact h35539
  rcases h17832 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u0)

theorem step36026 (p138 p189 p262 p310 p864 p980 p1055 p1325 p1349 : Prop)
    (h35668 : p138)
    (h28734 : (¬ p864) ∨ p980 ∨ (¬ p1349) ∨ p189 ∨ (¬ p1325) ∨ (¬ p310) ∨ (¬ p262) ∨ p1055 ∨ (¬ p138)) : (¬ p864) ∨ (¬ p1349) ∨ p980 ∨ p189 ∨ (¬ p1325) ∨ (¬ p310) ∨ (¬ p262) ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p864 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
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
  have u7 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p138 := by
    exact h35668
  rcases h28734 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)
  · exact False.elim (u7 q7)
  · exact False.elim (q8 u8)

theorem step36027 (p15 p16 p234 p1330 p1349 p1366 p1489 : Prop)
    (h35539 : p16)
    (h17864 : (¬ p15) ∨ (¬ p16) ∨ (¬ p234) ∨ (¬ p1330) ∨ (¬ p1349) ∨ (¬ p1366) ∨ (¬ p1489)) : (¬ p1349) ∨ (¬ p1330) ∨ (¬ p1366) ∨ (¬ p15) ∨ (¬ p1489) ∨ (¬ p234) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p16 := by
    exact h35539
  rcases h17864 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u4)

theorem step36028 (p156 p160 p185 p1252 p1353 p1489 : Prop)
    (h35659 : p156)
    (h18359 : (¬ p156) ∨ (¬ p160) ∨ (¬ p185) ∨ (¬ p1252) ∨ (¬ p1353) ∨ (¬ p1489)) : (¬ p160) ∨ (¬ p1489) ∨ (¬ p1252) ∨ (¬ p1353) ∨ (¬ p185) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1252 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1353 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p156 := by
    exact h35659
  rcases h18359 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u1)

theorem step36029 (p2 p84 p186 p422 p424 p495 p582 p1148 p1229 : Prop)
    (h35574 : p582)
    (h28782 : (¬ p1148) ∨ p424 ∨ p495 ∨ (¬ p84) ∨ p422 ∨ p2 ∨ (¬ p582) ∨ (¬ p186) ∨ p1229) : (¬ p1148) ∨ p424 ∨ p495 ∨ (¬ p84) ∨ p422 ∨ p2 ∨ (¬ p186) ∨ p1229 := by
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
  have u6 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p582 := by
    exact h35574
  rcases h28782 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u6)
  · exact False.elim (u7 q8)

theorem step36030 (p2 p17 p138 p186 p424 : Prop)
    (h35668 : p138)
    (h28785 : (¬ p186) ∨ p424 ∨ (¬ p138) ∨ p2 ∨ (¬ p17)) : p424 ∨ p2 ∨ (¬ p186) ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p2) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p138 := by
    exact h35668
  rcases h28785 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u3)

theorem step36031 (p2 p156 p185 p186 p424 : Prop)
    (h35659 : p156)
    (h28786 : (¬ p156) ∨ p424 ∨ (¬ p186) ∨ p2 ∨ (¬ p185)) : p424 ∨ p2 ∨ (¬ p186) ∨ (¬ p185) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p2) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p156 := by
    exact h35659
  rcases h28786 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u3)

theorem step36032 (p3 p163 p186 p267 p303 p327 p363 p382 p424 : Prop)
    (h35549 : p327)
    (h28791 : (¬ p363) ∨ p303 ∨ p163 ∨ (¬ p267) ∨ (¬ p327) ∨ (¬ p3) ∨ (¬ p186) ∨ (¬ p382) ∨ (¬ p424)) : p303 ∨ p163 ∨ (¬ p363) ∨ (¬ p267) ∨ (¬ p3) ∨ (¬ p186) ∨ (¬ p382) ∨ (¬ p424) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p363 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p267 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p327 := by
    exact h35549
  rcases h28791 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step36033 (p3 p163 p186 p327 p424 p434 p690 p821 : Prop)
    (h35549 : p327)
    (h28792 : (¬ p434) ∨ (¬ p690) ∨ (¬ p3) ∨ p163 ∨ (¬ p186) ∨ (¬ p327) ∨ (¬ p821) ∨ (¬ p424)) : (¬ p690) ∨ (¬ p434) ∨ (¬ p3) ∨ p163 ∨ (¬ p186) ∨ (¬ p821) ∨ (¬ p424) := by
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
  have u2 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p821 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p327 := by
    exact h35549
  rcases h28792 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step36034 (p3 p84 p163 p186 p424 p495 p582 p595 p1287 : Prop)
    (h35574 : p582)
    (h28793 : (¬ p186) ∨ (¬ p84) ∨ (¬ p3) ∨ p495 ∨ p163 ∨ p595 ∨ (¬ p424) ∨ (¬ p1287) ∨ (¬ p582)) : p163 ∨ (¬ p186) ∨ (¬ p3) ∨ (¬ p84) ∨ p495 ∨ p595 ∨ (¬ p424) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p163) := fun hu => hn (Or.inl hu)
  have u1 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p582 := by
    exact h35574
  rcases h28793 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (u4 q3)
  · exact False.elim (u0 q4)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u8)

theorem step36036 (p134 p195 p211 p1631 p1666 : Prop)
    (h35556 : p195)
    (h17417 : (¬ p134) ∨ (¬ p195) ∨ (¬ p211) ∨ (¬ p1631) ∨ (¬ p1666)) : (¬ p1666) ∨ (¬ p1631) ∨ (¬ p134) ∨ (¬ p211) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1666 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1631 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p195 := by
    exact h35556
  rcases h17417 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)

theorem step36037 (p63 p498 p582 p1604 p1631 : Prop)
    (h35574 : p582)
    (h28799 : (¬ p1604) ∨ (¬ p1631) ∨ (¬ p498) ∨ p63 ∨ (¬ p582)) : (¬ p1631) ∨ (¬ p1604) ∨ (¬ p498) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1631 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1604 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p582 := by
    exact h35574
  rcases h28799 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)

theorem step36038 (p11 p17 p86 p224 p228 p897 p1096 : Prop)
    (h35496 : p86)
    (h28810 : p11 ∨ p17 ∨ (¬ p228) ∨ (¬ p86) ∨ p1096 ∨ (¬ p897) ∨ (¬ p224)) : p11 ∨ p17 ∨ (¬ p228) ∨ p1096 ∨ (¬ p897) ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p11) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p86 := by
    exact h35496
  rcases h28810 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (u3 q4)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step36039 (p39 p68 p88 p101 p121 p124 p211 p228 p789 p790 : Prop)
    (h35495 : p39)
    (h28815 : (¬ p101) ∨ (¬ p124) ∨ (¬ p228) ∨ (¬ p211) ∨ (¬ p39) ∨ p789 ∨ (¬ p68) ∨ (¬ p121) ∨ p790 ∨ (¬ p88)) : p790 ∨ (¬ p124) ∨ (¬ p228) ∨ (¬ p211) ∨ p789 ∨ (¬ p68) ∨ (¬ p121) ∨ (¬ p101) ∨ (¬ p88) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p790) := fun hu => hn (Or.inl hu)
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
  have u4 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p39 := by
    exact h35495
  rcases h28815 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u9)
  · exact False.elim (u4 q5)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (u0 q8)
  · exact False.elim (q9 u8)

theorem step36040 (p14 p39 p63 p225 p303 p351 p382 p614 : Prop)
    (h35495 : p39)
    (h28853 : p225 ∨ (¬ p614) ∨ (¬ p63) ∨ (¬ p39) ∨ (¬ p351) ∨ (¬ p382) ∨ p303 ∨ (¬ p14)) : (¬ p63) ∨ (¬ p614) ∨ p225 ∨ (¬ p351) ∨ (¬ p382) ∨ p303 ∨ (¬ p14) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p614 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p39 := by
    exact h35495
  rcases h28853 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u6)

theorem step36041 (p17 p86 p258 p738 p756 p897 p1096 : Prop)
    (h35496 : p86)
    (h28872 : (¬ p756) ∨ (¬ p738) ∨ p258 ∨ p17 ∨ (¬ p86) ∨ p1096 ∨ (¬ p897)) : (¬ p756) ∨ p17 ∨ p258 ∨ (¬ p738) ∨ p1096 ∨ (¬ p897) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p738 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p86 := by
    exact h35496
  rcases h28872 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (u2 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u6)
  · exact False.elim (u4 q5)
  · exact False.elim (q6 u5)

theorem step36042 (p4 p10 p101 p668 p1076 : Prop)
    (h35527 : p668)
    (h28885 : (¬ p10) ∨ (¬ p4) ∨ (¬ p668) ∨ p1076 ∨ p101) : p101 ∨ p1076 ∨ (¬ p10) ∨ (¬ p4) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p101) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p668 := by
    exact h35527
  rcases h28885 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (u1 q3)
  · exact False.elim (u0 q4)

theorem step36043 (p4 p306 p420 p633 p668 p1055 : Prop)
    (h35527 : p668)
    (h28888 : (¬ p420) ∨ p1055 ∨ (¬ p668) ∨ (¬ p306) ∨ (¬ p633) ∨ (¬ p4)) : (¬ p420) ∨ p1055 ∨ (¬ p306) ∨ (¬ p633) ∨ (¬ p4) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p668 := by
    exact h35527
  rcases h28888 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step36044 (p3 p41 p125 p187 p265 p303 p533 p534 p1325 : Prop)
    (h35501 : p533)
    (h18787 : (¬ p3) ∨ (¬ p41) ∨ (¬ p125) ∨ (¬ p187) ∨ (¬ p265) ∨ (¬ p303) ∨ (¬ p533) ∨ (¬ p534) ∨ (¬ p1325)) : (¬ p534) ∨ (¬ p125) ∨ (¬ p3) ∨ (¬ p187) ∨ (¬ p1325) ∨ (¬ p41) ∨ (¬ p265) ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p533 := by
    exact h35501
  rcases h18787 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u0)
  · exact False.elim (q8 u4)

theorem step36046 (p3 p14 p234 p303 p331 p382 p519 p576 p816 : Prop)
    (h35686 : p331)
    (h28904 : p3 ∨ p576 ∨ (¬ p519) ∨ (¬ p303) ∨ (¬ p331) ∨ p382 ∨ (¬ p816) ∨ p234 ∨ (¬ p14)) : (¬ p519) ∨ p576 ∨ p3 ∨ (¬ p303) ∨ p382 ∨ (¬ p816) ∨ p234 ∨ (¬ p14) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p519 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p816 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p234) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p331 := by
    exact h35686
  rcases h28904 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u8)
  · exact False.elim (u4 q5)
  · exact False.elim (q6 u5)
  · exact False.elim (u6 q7)
  · exact False.elim (q8 u7)

theorem step36047 (p163 p225 p422 p664 p1038 : Prop)
    (h35502 : p664)
    (h28920 : (¬ p422) ∨ (¬ p1038) ∨ (¬ p664) ∨ (¬ p163) ∨ p225) : (¬ p422) ∨ (¬ p1038) ∨ (¬ p163) ∨ p225 := by
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
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p664 := by
    exact h35502
  rcases h28920 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)
  · exact False.elim (u3 q4)

theorem step36048 (p104 p124 p225 p263 p728 p1330 p1349 p1489 : Prop)
    (h35554 : p263)
    (h28927 : (¬ p728) ∨ (¬ p104) ∨ (¬ p1349) ∨ p225 ∨ (¬ p1330) ∨ (¬ p263) ∨ (¬ p1489) ∨ (¬ p124)) : (¬ p1349) ∨ (¬ p728) ∨ (¬ p104) ∨ p225 ∨ (¬ p1330) ∨ (¬ p1489) ∨ (¬ p124) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p263 := by
    exact h35554
  rcases h28927 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step36050 (p3 p16 p71 p225 p728 p1330 p1349 p1489 : Prop)
    (h35539 : p16)
    (h28935 : (¬ p728) ∨ (¬ p71) ∨ (¬ p1489) ∨ (¬ p16) ∨ (¬ p1330) ∨ (¬ p1349) ∨ (¬ p3) ∨ p225) : (¬ p1489) ∨ (¬ p728) ∨ (¬ p71) ∨ (¬ p1330) ∨ (¬ p1349) ∨ (¬ p3) ∨ p225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p71 := by
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
  have u5 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p16 := by
    exact h35539
  rcases h28935 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (u6 q7)

theorem step36051 (p86 p163 p189 p225 p595 p1287 p1325 : Prop)
    (h35496 : p86)
    (h28941 : p225 ∨ p189 ∨ p595 ∨ (¬ p163) ∨ (¬ p1287) ∨ (¬ p1325) ∨ (¬ p86)) : p595 ∨ p189 ∨ p225 ∨ (¬ p163) ∨ (¬ p1287) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p595) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p86 := by
    exact h35496
  rcases h28941 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)

theorem step36052 (p3 p11 p39 p68 p88 p126 p225 p261 p351 p961 : Prop)
    (h35495 : p39)
    (h28945 : (¬ p961) ∨ p11 ∨ p126 ∨ (¬ p351) ∨ p225 ∨ (¬ p39) ∨ (¬ p3) ∨ (¬ p68) ∨ (¬ p261) ∨ (¬ p88)) : p11 ∨ p126 ∨ (¬ p961) ∨ (¬ p351) ∨ p225 ∨ (¬ p3) ∨ (¬ p68) ∨ (¬ p261) ∨ (¬ p88) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p11) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p39 := by
    exact h35495
  rcases h28945 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u2)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step36053 (p135 p169 p185 p189 p225 p258 p664 p1076 : Prop)
    (h35502 : p664)
    (h28946 : p225 ∨ p185 ∨ (¬ p1076) ∨ (¬ p189) ∨ (¬ p664) ∨ (¬ p135) ∨ (¬ p169) ∨ (¬ p258)) : p185 ∨ (¬ p189) ∨ p225 ∨ (¬ p1076) ∨ (¬ p135) ∨ (¬ p169) ∨ (¬ p258) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p185) := fun hu => hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p169 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p664 := by
    exact h35502
  rcases h28946 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step36054 (p3 p17 p135 p185 p187 p225 p664 p1115 : Prop)
    (h35502 : p664)
    (h28952 : (¬ p1115) ∨ (¬ p3) ∨ (¬ p664) ∨ (¬ p185) ∨ p17 ∨ (¬ p187) ∨ p225 ∨ (¬ p135)) : (¬ p1115) ∨ (¬ p3) ∨ (¬ p185) ∨ p17 ∨ (¬ p187) ∨ p225 ∨ (¬ p135) := by
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
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p664 := by
    exact h35502
  rcases h28952 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u2)
  · exact False.elim (u3 q4)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u6)

theorem step36061 (p344 p455 p633 p664 p1079 : Prop)
    (h35502 : p664)
    (h28978 : p455 ∨ (¬ p1079) ∨ (¬ p664) ∨ (¬ p633) ∨ (¬ p344)) : p455 ∨ (¬ p633) ∨ (¬ p1079) ∨ (¬ p344) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1079 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p664 := by
    exact h35502
  rcases h28978 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)

theorem step36063 (p303 p347 p368 p382 p421 p537 p577 p836 p922 p1538 : Prop)
    (h35646 : p347)
    (h29008 : (¬ p537) ∨ (¬ p421) ∨ (¬ p836) ∨ (¬ p347) ∨ (¬ p1538) ∨ p382 ∨ (¬ p922) ∨ (¬ p303) ∨ (¬ p368) ∨ (¬ p577)) : (¬ p537) ∨ p382 ∨ (¬ p836) ∨ (¬ p1538) ∨ (¬ p421) ∨ (¬ p922) ∨ (¬ p303) ∨ (¬ p368) ∨ (¬ p577) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1538 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p922 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p303 := by
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
  have u9 : p347 := by
    exact h35646
  rcases h29008 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u3)
  · exact False.elim (u1 q5)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step36064 (p63 p303 p347 p382 p617 p836 p918 : Prop)
    (h35646 : p347)
    (h29010 : p382 ∨ (¬ p918) ∨ (¬ p347) ∨ (¬ p617) ∨ (¬ p836) ∨ (¬ p303) ∨ p63) : (¬ p918) ∨ p382 ∨ (¬ p617) ∨ (¬ p836) ∨ (¬ p303) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p617 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p347 := by
    exact h35646
  rcases h29010 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)

theorem step36065 (p224 p244 p382 p680 p836 : Prop)
    (h35498 : p244)
    (h29013 : p382 ∨ (¬ p836) ∨ (¬ p224) ∨ (¬ p244) ∨ (¬ p680)) : (¬ p836) ∨ p382 ∨ (¬ p224) ∨ (¬ p680) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p244 := by
    exact h35498
  rcases h29013 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)

theorem step36067 (p63 p303 p347 p382 p615 p897 p1096 p1389 : Prop)
    (h35646 : p347)
    (h29025 : (¬ p615) ∨ (¬ p1389) ∨ (¬ p303) ∨ (¬ p897) ∨ p1096 ∨ (¬ p347) ∨ p382 ∨ (¬ p63)) : (¬ p615) ∨ (¬ p1389) ∨ (¬ p303) ∨ (¬ p897) ∨ p1096 ∨ p382 ∨ (¬ p63) := by
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
  have u5 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p347 := by
    exact h35646
  rcases h29025 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u7)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u6)

theorem step36068 (p668 p835 p918 p1115 p1385 : Prop)
    (h35527 : p668)
    (h29044 : p918 ∨ (¬ p835) ∨ (¬ p668) ∨ (¬ p1385) ∨ p1115) : (¬ p1385) ∨ (¬ p835) ∨ p918 ∨ p1115 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p835 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p668 := by
    exact h35527
  rcases h29044 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (u3 q4)

theorem step36069 (p185 p668 p790 p835 p1115 : Prop)
    (h35527 : p668)
    (h29045 : p790 ∨ p185 ∨ (¬ p668) ∨ (¬ p835) ∨ p1115) : (¬ p835) ∨ p790 ∨ p185 ∨ p1115 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p835 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p790) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p668 := by
    exact h35527
  rcases h29045 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (u3 q4)

theorem step36070 (p185 p286 p668 p790 p835 p1076 : Prop)
    (h35527 : p668)
    (h29047 : p790 ∨ p185 ∨ (¬ p286) ∨ (¬ p835) ∨ p1076 ∨ (¬ p668)) : (¬ p286) ∨ p790 ∨ p185 ∨ (¬ p835) ∨ p1076 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p790) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p835 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p668 := by
    exact h35527
  rcases h29047 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u5)

theorem step36071 (p158 p668 p835 p918 p1055 p1385 : Prop)
    (h35527 : p668)
    (h29048 : p918 ∨ p1055 ∨ (¬ p158) ∨ (¬ p835) ∨ (¬ p1385) ∨ (¬ p668)) : p1055 ∨ p918 ∨ (¬ p158) ∨ (¬ p835) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1055) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p668 := by
    exact h35527
  rcases h29048 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)

theorem step36072 (p17 p89 p224 p382 p576 p709 p838 p1103 p1385 : Prop)
    (h35504 : p1103)
    (h29116 : p17 ∨ (¬ p709) ∨ (¬ p576) ∨ (¬ p89) ∨ p224 ∨ p1385 ∨ (¬ p382) ∨ (¬ p838) ∨ (¬ p1103)) : (¬ p576) ∨ p17 ∨ (¬ p709) ∨ (¬ p89) ∨ p224 ∨ p1385 ∨ (¬ p382) ∨ (¬ p838) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p709 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1103 := by
    exact h35504
  rcases h29116 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u8)

theorem step36073 (p63 p126 p224 p347 p382 p576 p709 p1103 : Prop)
    (h35504 : p1103)
    (h35646 : p347)
    (h29117 : p576 ∨ (¬ p709) ∨ p224 ∨ (¬ p126) ∨ (¬ p63) ∨ (¬ p1103) ∨ (¬ p347) ∨ (¬ p382)) : p576 ∨ (¬ p709) ∨ p224 ∨ (¬ p126) ∨ (¬ p63) ∨ (¬ p382) := by
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
  have u5 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1103 := by
    exact h35504
  have u7 : p347 := by
    exact h35646
  rcases h29117 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u5)

theorem step36074 (p382 p495 p582 p614 p1286 p1392 : Prop)
    (h35574 : p582)
    (h29135 : (¬ p1286) ∨ p495 ∨ (¬ p614) ∨ (¬ p582) ∨ (¬ p1392) ∨ (¬ p382)) : (¬ p614) ∨ (¬ p1286) ∨ p495 ∨ (¬ p1392) ∨ (¬ p382) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p614 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1392 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p582 := by
    exact h35574
  rcases h29135 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step36076 (p16 p121 p134 p189 p389 p595 p1286 : Prop)
    (h35539 : p16)
    (h29139 : p121 ∨ (¬ p389) ∨ (¬ p134) ∨ (¬ p16) ∨ (¬ p595) ∨ (¬ p189) ∨ (¬ p1286)) : (¬ p389) ∨ (¬ p595) ∨ (¬ p134) ∨ p121 ∨ (¬ p189) ∨ (¬ p1286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p121) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p16 := by
    exact h35539
  rcases h29139 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step36083 (p595 p668 p899 p1095 p1096 : Prop)
    (h35527 : p668)
    (h29181 : (¬ p1096) ∨ (¬ p899) ∨ (¬ p668) ∨ (¬ p1095) ∨ p595) : (¬ p1095) ∨ (¬ p1096) ∨ (¬ p899) ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p899 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p668 := by
    exact h35527
  rcases h29181 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (u3 q4)

theorem step36085 (p8 p303 p347 p666 p1095 p1102 : Prop)
    (h35646 : p347)
    (h29184 : (¬ p1095) ∨ p8 ∨ (¬ p1102) ∨ (¬ p666) ∨ (¬ p303) ∨ (¬ p347)) : (¬ p1095) ∨ (¬ p1102) ∨ p8 ∨ (¬ p666) ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p666 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p347 := by
    exact h35646
  rcases h29184 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)

theorem step36086 (p16 p189 p419 p424 p665 p1095 p1096 : Prop)
    (h35539 : p16)
    (h29188 : p424 ∨ (¬ p1095) ∨ (¬ p665) ∨ (¬ p1096) ∨ (¬ p16) ∨ (¬ p189) ∨ (¬ p419)) : (¬ p1095) ∨ p424 ∨ (¬ p665) ∨ (¬ p1096) ∨ (¬ p189) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p424) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p16 := by
    exact h35539
  rcases h29188 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step36087 (p16 p790 p980 p1015 p1095 p1096 p1335 : Prop)
    (h35539 : p16)
    (h29189 : (¬ p1096) ∨ p980 ∨ (¬ p16) ∨ (¬ p1335) ∨ p790 ∨ (¬ p1015) ∨ (¬ p1095)) : (¬ p1096) ∨ p790 ∨ (¬ p1335) ∨ p980 ∨ (¬ p1015) ∨ (¬ p1095) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p790) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p16 := by
    exact h35539
  rcases h29189 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (u1 q4)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step36088 (p16 p163 p189 p225 p668 p1095 p1096 : Prop)
    (h35539 : p16)
    (h35527 : p668)
    (h29193 : p163 ∨ (¬ p225) ∨ (¬ p1096) ∨ (¬ p189) ∨ (¬ p16) ∨ (¬ p668) ∨ (¬ p1095)) : (¬ p1096) ∨ p163 ∨ (¬ p225) ∨ (¬ p189) ∨ (¬ p1095) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p16 := by
    exact h35539
  have u6 : p668 := by
    exact h35527
  rcases h29193 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u4)

theorem step36089 (p347 p438 p617 p687 p897 p1055 p1095 p1097 : Prop)
    (h35646 : p347)
    (h17179 : (¬ p347) ∨ (¬ p438) ∨ (¬ p617) ∨ (¬ p687) ∨ (¬ p897) ∨ (¬ p1055) ∨ (¬ p1095) ∨ (¬ p1097)) : (¬ p1095) ∨ (¬ p687) ∨ (¬ p897) ∨ (¬ p1097) ∨ (¬ p617) ∨ (¬ p438) ∨ (¬ p1055) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1097 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p617 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p347 := by
    exact h35646
  rcases h17179 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u3)

theorem step36090 (p63 p124 p344 p425 p582 p668 p1095 p1096 : Prop)
    (h35527 : p668)
    (h35574 : p582)
    (h29195 : p124 ∨ (¬ p425) ∨ (¬ p1095) ∨ (¬ p668) ∨ p344 ∨ (¬ p1096) ∨ (¬ p582) ∨ p63) : (¬ p1095) ∨ p124 ∨ (¬ p425) ∨ p344 ∨ (¬ p1096) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p668 := by
    exact h35527
  have u7 : p582 := by
    exact h35574
  rcases h29195 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (u3 q4)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u7)
  · exact False.elim (u5 q7)

theorem step36091 (p38 p49 p63 p124 p206 p344 p668 p1095 p1096 : Prop)
    (h35527 : p668)
    (h29196 : p124 ∨ (¬ p1096) ∨ (¬ p668) ∨ (¬ p1095) ∨ (¬ p38) ∨ (¬ p206) ∨ p63 ∨ p344 ∨ (¬ p49)) : (¬ p1095) ∨ (¬ p1096) ∨ p124 ∨ (¬ p38) ∨ (¬ p206) ∨ p63 ∨ p344 ∨ (¬ p49) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p668 := by
    exact h35527
  rcases h29196 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)
  · exact False.elim (u6 q7)
  · exact False.elim (q8 u7)

theorem step36092 (p4 p124 p125 p255 p668 p1115 : Prop)
    (h35527 : p668)
    (h29213 : (¬ p125) ∨ (¬ p255) ∨ (¬ p4) ∨ (¬ p668) ∨ p1115 ∨ (¬ p124)) : (¬ p125) ∨ (¬ p255) ∨ (¬ p4) ∨ p1115 ∨ (¬ p124) := by
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
  have u3 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p668 := by
    exact h35527
  rcases h29213 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (u3 q4)
  · exact False.elim (q5 u4)

theorem step36093 (p86 p185 p303 p420 p495 p665 p1115 : Prop)
    (h35496 : p86)
    (h29219 : (¬ p420) ∨ (¬ p495) ∨ (¬ p86) ∨ p1115 ∨ p185 ∨ (¬ p665) ∨ (¬ p303)) : (¬ p420) ∨ (¬ p495) ∨ p1115 ∨ p185 ∨ (¬ p665) ∨ (¬ p303) := by
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
  have u2 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p86 := by
    exact h35496
  rcases h29219 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (u2 q3)
  · exact False.elim (u3 q4)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step36120 (p15 p16 p185 p980 p1115 p1469 p1712 : Prop)
    (h35539 : p16)
    (h17714 : (¬ p15) ∨ (¬ p16) ∨ (¬ p185) ∨ (¬ p980) ∨ (¬ p1115) ∨ (¬ p1469) ∨ (¬ p1712)) : (¬ p1115) ∨ (¬ p1712) ∨ (¬ p185) ∨ (¬ p1469) ∨ (¬ p980) ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1712 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1469 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p16 := by
    exact h35539
  rcases h17714 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u1)

theorem step36121 (p16 p185 p495 p980 p1115 p1449 p1611 : Prop)
    (h35539 : p16)
    (h29281 : (¬ p1115) ∨ (¬ p1611) ∨ (¬ p1449) ∨ p495 ∨ (¬ p185) ∨ (¬ p980) ∨ (¬ p16)) : (¬ p1115) ∨ (¬ p1611) ∨ (¬ p1449) ∨ p495 ∨ (¬ p185) ∨ (¬ p980) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p16 := by
    exact h35539
  rcases h29281 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)

theorem step36122 (p125 p185 p263 p434 p980 p1115 p1330 : Prop)
    (h35554 : p263)
    (h29283 : (¬ p434) ∨ (¬ p1115) ∨ (¬ p263) ∨ (¬ p980) ∨ p125 ∨ (¬ p185) ∨ (¬ p1330)) : (¬ p1115) ∨ (¬ p434) ∨ (¬ p980) ∨ p125 ∨ (¬ p185) ∨ (¬ p1330) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p263 := by
    exact h35554
  rcases h29283 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (u3 q4)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step36123 (p157 p160 p244 p980 p1115 : Prop)
    (h35498 : p244)
    (h16466 : (¬ p157) ∨ (¬ p160) ∨ (¬ p244) ∨ (¬ p980) ∨ (¬ p1115)) : (¬ p160) ∨ (¬ p157) ∨ (¬ p980) ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p157 := by
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
  have u4 : p244 := by
    exact h35498
  rcases h16466 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)

theorem step36124 (p101 p121 p124 p263 p1226 p1347 p1442 p1508 : Prop)
    (h35554 : p263)
    (h17833 : (¬ p101) ∨ (¬ p121) ∨ (¬ p124) ∨ (¬ p263) ∨ (¬ p1226) ∨ (¬ p1347) ∨ (¬ p1442) ∨ (¬ p1508)) : (¬ p1347) ∨ (¬ p124) ∨ (¬ p101) ∨ (¬ p1508) ∨ (¬ p1226) ∨ (¬ p121) ∨ (¬ p1442) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1442 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p263 := by
    exact h35554
  rcases h17833 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u3)

theorem step36125 (p87 p1226 p1273 p1347 p1508 : Prop)
    (h35497 : p87)
    (h18012 : (¬ p87) ∨ (¬ p1226) ∨ (¬ p1273) ∨ (¬ p1347) ∨ (¬ p1508)) : (¬ p1226) ∨ (¬ p1508) ∨ (¬ p1273) ∨ (¬ p1347) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1508 := by
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
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p87 := by
    exact h35497
  rcases h18012 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)

theorem step36127 (p2 p303 p331 p1001 p1140 : Prop)
    (h35686 : p331)
    (h19758 : (¬ p2) ∨ (¬ p303) ∨ (¬ p331) ∨ (¬ p1001) ∨ (¬ p1140)) : (¬ p1140) ∨ (¬ p303) ∨ (¬ p1001) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1001 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p331 := by
    exact h35686
  rcases h19758 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u0)

theorem step36128 (p64 p86 p206 p389 p455 p789 p790 p1611 p1624 : Prop)
    (h35496 : p86)
    (h29369 : (¬ p1611) ∨ (¬ p1624) ∨ (¬ p789) ∨ (¬ p389) ∨ (¬ p790) ∨ (¬ p64) ∨ p455 ∨ (¬ p86) ∨ (¬ p206)) : (¬ p1624) ∨ (¬ p1611) ∨ (¬ p789) ∨ (¬ p389) ∨ (¬ p790) ∨ (¬ p64) ∨ p455 ∨ (¬ p206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1624 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1611 := by
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
  have u7 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p86 := by
    exact h35496
  rcases h29369 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u7)

theorem step36129 (p10 p15 p24 p39 p88 p382 p495 p521 p789 p815 : Prop)
    (h35495 : p39)
    (h29373 : (¬ p24) ∨ p15 ∨ (¬ p521) ∨ (¬ p382) ∨ (¬ p39) ∨ (¬ p789) ∨ (¬ p88) ∨ p495 ∨ (¬ p815) ∨ p10) : (¬ p382) ∨ p15 ∨ (¬ p24) ∨ (¬ p521) ∨ (¬ p789) ∨ (¬ p88) ∨ p495 ∨ (¬ p815) ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p521 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p815 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p39 := by
    exact h35495
  rcases h29373 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u2)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (u6 q7)
  · exact False.elim (q8 u7)
  · exact False.elim (u8 q9)

theorem step36130 (p347 p438 p736 p897 p1562 : Prop)
    (h35646 : p347)
    (h17452 : (¬ p347) ∨ (¬ p438) ∨ (¬ p736) ∨ (¬ p897) ∨ (¬ p1562)) : (¬ p736) ∨ (¬ p1562) ∨ (¬ p897) ∨ (¬ p438) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p736 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1562 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p347 := by
    exact h35646
  rcases h17452 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u1)

theorem step36131 (p11 p16 p17 p532 p533 p1096 p1562 : Prop)
    (h35539 : p16)
    (h35501 : p533)
    (h19132 : (¬ p11) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p532) ∨ (¬ p533) ∨ (¬ p1096) ∨ (¬ p1562)) : (¬ p1562) ∨ (¬ p532) ∨ (¬ p17) ∨ (¬ p11) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1562 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p16 := by
    exact h35539
  have u6 : p533 := by
    exact h35501
  rcases h19132 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u0)

theorem step36132 (p2 p5 p419 p533 p1096 p1325 p1562 : Prop)
    (h35501 : p533)
    (h18362 : (¬ p2) ∨ (¬ p5) ∨ (¬ p419) ∨ (¬ p533) ∨ (¬ p1096) ∨ (¬ p1325) ∨ (¬ p1562)) : (¬ p1562) ∨ (¬ p1096) ∨ (¬ p5) ∨ (¬ p419) ∨ (¬ p1325) ∨ (¬ p2) := by
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
  have u2 : p5 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p533 := by
    exact h35501
  rcases h18362 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u0)

theorem step36133 (p49 p63 p423 p533 p1096 p1465 p1562 : Prop)
    (h35501 : p533)
    (h29391 : (¬ p1562) ∨ p63 ∨ (¬ p1096) ∨ (¬ p49) ∨ (¬ p1465) ∨ (¬ p533) ∨ p423) : (¬ p1562) ∨ (¬ p1096) ∨ p63 ∨ (¬ p49) ∨ (¬ p1465) ∨ p423 := by
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
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p423) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p533 := by
    exact h35501
  rcases h29391 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)
  · exact False.elim (u5 q6)

theorem step36134 (p5 p6 p121 p532 p533 p1096 p1562 : Prop)
    (h35501 : p533)
    (h29392 : (¬ p1562) ∨ p121 ∨ (¬ p1096) ∨ (¬ p6) ∨ (¬ p532) ∨ (¬ p533) ∨ (¬ p5)) : (¬ p1562) ∨ (¬ p1096) ∨ p121 ∨ (¬ p6) ∨ (¬ p532) ∨ (¬ p5) := by
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
  have u2 : (¬ p121) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p533 := by
    exact h35501
  rcases h29392 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u5)

theorem step36135 (p4 p8 p189 p263 p303 p310 p1325 p1473 p1711 : Prop)
    (h35554 : p263)
    (h29395 : (¬ p1711) ∨ (¬ p263) ∨ (¬ p310) ∨ (¬ p4) ∨ (¬ p1473) ∨ (¬ p189) ∨ (¬ p8) ∨ p1325 ∨ p303) : p303 ∨ (¬ p1711) ∨ (¬ p310) ∨ (¬ p4) ∨ (¬ p1473) ∨ (¬ p189) ∨ (¬ p8) ∨ p1325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p1711 := by
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
  have u7 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p263 := by
    exact h35554
  rcases h29395 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)
  · exact False.elim (u7 q7)
  · exact False.elim (u0 q8)

theorem step36136 (p15 p124 p496 p980 p1076 p1473 p1710 : Prop)
    (h35500 : p496)
    (h29396 : (¬ p1710) ∨ (¬ p1473) ∨ (¬ p124) ∨ p980 ∨ (¬ p496) ∨ p1076 ∨ p15) : (¬ p1710) ∨ p1076 ∨ (¬ p124) ∨ p980 ∨ (¬ p1473) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1473 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p496 := by
    exact h35500
  rcases h29396 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u6)
  · exact False.elim (u1 q5)
  · exact False.elim (u5 q6)

theorem step36137 (p138 p382 p576 p797 p819 p1286 p1392 : Prop)
    (h35668 : p138)
    (h18257 : (¬ p138) ∨ (¬ p382) ∨ (¬ p576) ∨ (¬ p797) ∨ (¬ p819) ∨ (¬ p1286) ∨ (¬ p1392)) : (¬ p797) ∨ (¬ p1392) ∨ (¬ p1286) ∨ (¬ p382) ∨ (¬ p819) ∨ (¬ p576) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p797 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1392 := by
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
  have u4 : p819 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p138 := by
    exact h35668
  rcases h18257 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u1)

theorem step36139 (p84 p125 p185 p425 p438 p582 p980 p1115 p1335 : Prop)
    (h35574 : p582)
    (h29487 : p980 ∨ p185 ∨ (¬ p425) ∨ (¬ p582) ∨ (¬ p84) ∨ (¬ p438) ∨ p1115 ∨ (¬ p125) ∨ (¬ p1335)) : p185 ∨ p980 ∨ (¬ p425) ∨ (¬ p84) ∨ (¬ p438) ∨ p1115 ∨ (¬ p125) ∨ (¬ p1335) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p185) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p582 := by
    exact h35574
  rcases h29487 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step36140 (p84 p495 p582 p980 p1229 p1313 p1346 p1508 : Prop)
    (h35574 : p582)
    (h29510 : p495 ∨ (¬ p1346) ∨ (¬ p582) ∨ (¬ p1313) ∨ p1229 ∨ (¬ p84) ∨ (¬ p980) ∨ (¬ p1508)) : (¬ p1313) ∨ (¬ p1346) ∨ p495 ∨ p1229 ∨ (¬ p84) ∨ (¬ p980) ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1313 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p582 := by
    exact h35574
  rcases h29510 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u0)
  · exact False.elim (u3 q4)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step36141 (p161 p668 p897 p980 p1311 : Prop)
    (h35527 : p668)
    (h29513 : (¬ p980) ∨ (¬ p1311) ∨ (¬ p897) ∨ p161 ∨ (¬ p668)) : p161 ∨ (¬ p1311) ∨ (¬ p897) ∨ (¬ p980) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p161) := fun hu => hn (Or.inl hu)
  have u1 : p1311 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p668 := by
    exact h35527
  rcases h29513 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)

theorem step36142 (p15 p39 p88 p980 p1229 p1309 p1349 p1489 : Prop)
    (h35495 : p39)
    (h29516 : (¬ p1489) ∨ p980 ∨ (¬ p1229) ∨ (¬ p88) ∨ (¬ p1349) ∨ (¬ p39) ∨ p15 ∨ (¬ p1309)) : (¬ p1489) ∨ (¬ p1229) ∨ p980 ∨ (¬ p88) ∨ (¬ p1349) ∨ p15 ∨ (¬ p1309) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p39 := by
    exact h35495
  rcases h29516 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u7)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u6)

theorem step36143 (p664 p897 p1096 p1229 p1307 : Prop)
    (h35502 : p664)
    (h29518 : p1229 ∨ (¬ p1307) ∨ p897 ∨ (¬ p1096) ∨ (¬ p664)) : p897 ∨ p1229 ∨ (¬ p1307) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p897) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1307 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p664 := by
    exact h35502
  rcases h29518 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)

theorem step36144 (p63 p124 p224 p344 p425 p582 p1229 p1291 : Prop)
    (h35574 : p582)
    (h29524 : p124 ∨ p344 ∨ (¬ p1229) ∨ p63 ∨ (¬ p425) ∨ (¬ p1291) ∨ (¬ p224) ∨ (¬ p582)) : (¬ p1229) ∨ p124 ∨ p344 ∨ p63 ∨ (¬ p425) ∨ (¬ p1291) ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p582 := by
    exact h35574
  rcases h29524 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u7)

theorem step36146 (p195 p1035 p1140 p1252 p1489 : Prop)
    (h35556 : p195)
    (h16704 : (¬ p195) ∨ (¬ p1035) ∨ (¬ p1140) ∨ (¬ p1252) ∨ (¬ p1489)) : (¬ p1489) ∨ (¬ p1252) ∨ (¬ p1140) ∨ (¬ p1035) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1252 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p195 := by
    exact h35556
  rcases h16704 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)

theorem step36149 (p138 p189 p262 p368 p382 p384 p980 p1124 p1349 p1452 : Prop)
    (h35668 : p138)
    (h29648 : p382 ∨ (¬ p1452) ∨ (¬ p1124) ∨ (¬ p262) ∨ p189 ∨ (¬ p384) ∨ (¬ p368) ∨ (¬ p1349) ∨ (¬ p980) ∨ (¬ p138)) : (¬ p1452) ∨ p382 ∨ (¬ p1124) ∨ (¬ p262) ∨ p189 ∨ (¬ p384) ∨ (¬ p368) ∨ (¬ p1349) ∨ (¬ p980) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p138 := by
    exact h35668
  rcases h29648 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u8)
  · exact False.elim (q9 u9)

theorem step36151 (p86 p185 p595 p665 p980 p1122 p1287 p1508 : Prop)
    (h35496 : p86)
    (h29652 : (¬ p1508) ∨ p185 ∨ (¬ p665) ∨ (¬ p1122) ∨ (¬ p980) ∨ p595 ∨ (¬ p86) ∨ (¬ p1287)) : p185 ∨ (¬ p1508) ∨ (¬ p665) ∨ (¬ p1122) ∨ (¬ p980) ∨ p595 ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p185) := fun hu => hn (Or.inl hu)
  have u1 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
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
  have u6 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p86 := by
    exact h35496
  rcases h29652 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u6)

theorem step36152 (p8 p161 p224 p228 p532 p1103 p1229 : Prop)
    (h35504 : p1103)
    (h29660 : p161 ∨ (¬ p1229) ∨ p8 ∨ (¬ p1103) ∨ (¬ p224) ∨ (¬ p228) ∨ (¬ p532)) : p161 ∨ (¬ p1229) ∨ p8 ∨ (¬ p224) ∨ (¬ p228) ∨ (¬ p532) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p161) := fun hu => hn (Or.inl hu)
  have u1 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1103 := by
    exact h35504
  rcases h29660 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step36153 (p41 p63 p106 p163 p1055 p1076 p1103 : Prop)
    (h35504 : p1103)
    (h29661 : (¬ p41) ∨ (¬ p1055) ∨ p1076 ∨ (¬ p63) ∨ (¬ p106) ∨ (¬ p1103) ∨ (¬ p163)) : (¬ p163) ∨ (¬ p63) ∨ p1076 ∨ (¬ p1055) ∨ (¬ p41) ∨ (¬ p106) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1103 := by
    exact h35504
  rcases h29661 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u0)

theorem step36154 (p8 p11 p17 p86 p897 p1074 p1081 p1097 : Prop)
    (h35496 : p86)
    (h29677 : (¬ p1074) ∨ p17 ∨ (¬ p1081) ∨ p11 ∨ p8 ∨ p897 ∨ (¬ p1097) ∨ (¬ p86)) : p11 ∨ p17 ∨ (¬ p1081) ∨ (¬ p1074) ∨ p8 ∨ p897 ∨ (¬ p1097) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p11) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1097 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p86 := by
    exact h35496
  rcases h29677 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u3)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (u0 q3)
  · exact False.elim (u4 q4)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u7)

theorem step36156 (p11 p17 p86 p161 p980 p1081 p1229 : Prop)
    (h35496 : p86)
    (h29679 : p980 ∨ (¬ p161) ∨ p1229 ∨ p11 ∨ p17 ∨ (¬ p1081) ∨ (¬ p86)) : (¬ p161) ∨ p1229 ∨ p980 ∨ p11 ∨ p17 ∨ (¬ p1081) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p86 := by
    exact h35496
  rcases h29679 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u1 q2)
  · exact False.elim (u3 q3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)

theorem step36157 (p16 p125 p185 p420 p455 p498 p1081 p1115 : Prop)
    (h35539 : p16)
    (h29681 : (¬ p420) ∨ (¬ p1115) ∨ (¬ p16) ∨ (¬ p455) ∨ p125 ∨ (¬ p498) ∨ (¬ p185) ∨ (¬ p1081)) : (¬ p1115) ∨ (¬ p420) ∨ (¬ p455) ∨ p125 ∨ (¬ p498) ∨ (¬ p185) ∨ (¬ p1081) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
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
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p16 := by
    exact h35539
  rcases h29681 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u2)
  · exact False.elim (u3 q4)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step36158 (p11 p125 p126 p496 p1074 p1081 p1096 : Prop)
    (h35500 : p496)
    (h29682 : p126 ∨ p125 ∨ p11 ∨ p1096 ∨ (¬ p496) ∨ (¬ p1074) ∨ (¬ p1081)) : p11 ∨ p126 ∨ p125 ∨ p1096 ∨ (¬ p1074) ∨ (¬ p1081) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p11) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p496 := by
    exact h35500
  rcases h29682 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (u0 q2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step36159 (p8 p664 p980 p1056 p1226 : Prop)
    (h35502 : p664)
    (h29683 : (¬ p1226) ∨ (¬ p8) ∨ p980 ∨ (¬ p664) ∨ (¬ p1056)) : (¬ p1226) ∨ p980 ∨ (¬ p8) ∨ (¬ p1056) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1056 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p664 := by
    exact h35502
  rcases h29683 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)

theorem step36160 (p15 p110 p125 p126 p258 p423 p496 p1042 : Prop)
    (h35500 : p496)
    (h29694 : p126 ∨ (¬ p110) ∨ p15 ∨ (¬ p496) ∨ p125 ∨ p258 ∨ p423 ∨ (¬ p1042)) : p126 ∨ p15 ∨ (¬ p110) ∨ p125 ∨ p258 ∨ p423 ∨ (¬ p1042) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p423) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1042 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p496 := by
    exact h35500
  rcases h29694 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u7)
  · exact False.elim (u3 q4)
  · exact False.elim (u4 q5)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u6)

theorem step36161 (p160 p495 p633 p1040 p1076 p1233 p1465 : Prop)
    (h35505 : p1233)
    (h29695 : p633 ∨ (¬ p495) ∨ (¬ p160) ∨ (¬ p1233) ∨ (¬ p1465) ∨ (¬ p1076) ∨ (¬ p1040)) : (¬ p160) ∨ p633 ∨ (¬ p495) ∨ (¬ p1465) ∨ (¬ p1076) ∨ (¬ p1040) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p633) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1040 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1233 := by
    exact h35505
  rcases h29695 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step36162 (p15 p227 p423 p496 p1004 p1325 p1452 : Prop)
    (h35500 : p496)
    (h29703 : (¬ p1004) ∨ p423 ∨ (¬ p1452) ∨ (¬ p496) ∨ (¬ p1325) ∨ (¬ p227) ∨ p15) : p423 ∨ (¬ p1452) ∨ (¬ p1004) ∨ (¬ p1325) ∨ (¬ p227) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p496 := by
    exact h35500
  rcases h29703 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)

theorem step36163 (p3 p14 p83 p160 p188 p423 p1004 p1233 p1325 : Prop)
    (h35505 : p1233)
    (h29704 : p423 ∨ (¬ p1004) ∨ (¬ p14) ∨ (¬ p1233) ∨ (¬ p1325) ∨ p3 ∨ (¬ p160) ∨ (¬ p188) ∨ (¬ p83)) : p423 ∨ (¬ p14) ∨ (¬ p1004) ∨ (¬ p1325) ∨ p3 ∨ (¬ p160) ∨ (¬ p188) ∨ (¬ p83) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1233 := by
    exact h35505
  rcases h29704 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u3)
  · exact False.elim (u4 q5)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step36164 (p15 p17 p86 p126 p303 p423 p1004 : Prop)
    (h35496 : p86)
    (h29705 : (¬ p1004) ∨ p303 ∨ p17 ∨ (¬ p126) ∨ (¬ p86) ∨ p15 ∨ p423) : p303 ∨ p17 ∨ (¬ p1004) ∨ (¬ p126) ∨ p15 ∨ p423 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p423) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p86 := by
    exact h35496
  rcases h29705 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (u4 q5)
  · exact False.elim (u5 q6)

theorem step36165 (p3 p14 p64 p86 p423 p789 p790 p1004 : Prop)
    (h35496 : p86)
    (h29706 : p423 ∨ (¬ p1004) ∨ (¬ p14) ∨ (¬ p64) ∨ p3 ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p86)) : p423 ∨ (¬ p14) ∨ (¬ p1004) ∨ (¬ p64) ∨ p3 ∨ (¬ p789) ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1004 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p86 := by
    exact h35496
  rcases h29706 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u7)

theorem step36166 (p15 p86 p185 p224 p423 p836 p1004 : Prop)
    (h35496 : p86)
    (h29707 : (¬ p1004) ∨ p185 ∨ p15 ∨ p224 ∨ p836 ∨ (¬ p86) ∨ p423) : p185 ∨ p224 ∨ p15 ∨ (¬ p1004) ∨ p836 ∨ p423 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p185) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p423) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p86 := by
    exact h35496
  rcases h29707 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (u0 q1)
  · exact False.elim (u2 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u6)
  · exact False.elim (u5 q6)

theorem step36167 (p16 p189 p224 p422 p897 p1004 p1096 : Prop)
    (h35539 : p16)
    (h29708 : (¬ p422) ∨ (¬ p1004) ∨ p224 ∨ (¬ p16) ∨ (¬ p189) ∨ p897 ∨ (¬ p1096)) : p897 ∨ (¬ p422) ∨ p224 ∨ (¬ p189) ∨ (¬ p1004) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p897) := fun hu => hn (Or.inl hu)
  have u1 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p16 := by
    exact h35539
  rcases h29708 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (u0 q5)
  · exact False.elim (q6 u5)

theorem step36168 (p3 p16 p163 p188 p422 p595 p1004 p1286 : Prop)
    (h35539 : p16)
    (h29709 : (¬ p422) ∨ (¬ p1286) ∨ (¬ p188) ∨ (¬ p595) ∨ (¬ p163) ∨ (¬ p1004) ∨ p3 ∨ (¬ p16)) : (¬ p595) ∨ (¬ p422) ∨ (¬ p188) ∨ (¬ p1286) ∨ (¬ p163) ∨ (¬ p1004) ∨ p3 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1286 := by
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
  have u6 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p16 := by
    exact h35539
  rcases h29709 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)
  · exact False.elim (q7 u7)

theorem step36169 (p15 p124 p224 p344 p423 p496 p1004 : Prop)
    (h35500 : p496)
    (h29710 : (¬ p1004) ∨ (¬ p124) ∨ (¬ p496) ∨ p15 ∨ p224 ∨ (¬ p344) ∨ p423) : (¬ p344) ∨ (¬ p124) ∨ p15 ∨ p224 ∨ (¬ p1004) ∨ p423 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p423) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p496 := by
    exact h35500
  rcases h29710 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (u2 q3)
  · exact False.elim (u3 q4)
  · exact False.elim (q5 u0)
  · exact False.elim (u5 q6)

theorem step36170 (p3 p14 p64 p125 p303 p423 p496 p1004 : Prop)
    (h35500 : p496)
    (h29711 : p423 ∨ p3 ∨ p125 ∨ (¬ p496) ∨ p303 ∨ (¬ p64) ∨ (¬ p1004) ∨ (¬ p14)) : p423 ∨ p3 ∨ p125 ∨ p303 ∨ (¬ p64) ∨ (¬ p1004) ∨ (¬ p14) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p496 := by
    exact h35500
  rcases h29711 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u7)
  · exact False.elim (u3 q4)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step36171 (p125 p189 p224 p263 p303 p422 p545 p1002 : Prop)
    (h35554 : p263)
    (h29748 : (¬ p1002) ∨ p303 ∨ (¬ p189) ∨ (¬ p422) ∨ (¬ p545) ∨ (¬ p224) ∨ (¬ p263) ∨ p125) : p303 ∨ (¬ p189) ∨ (¬ p1002) ∨ (¬ p422) ∨ (¬ p545) ∨ (¬ p224) ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1002 := by
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
  have u6 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p263 := by
    exact h35554
  rcases h29748 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u7)
  · exact False.elim (u6 q7)

theorem step36173 (p331 p381 p419 p532 p1325 : Prop)
    (h35686 : p331)
    (h29772 : p419 ∨ p1325 ∨ (¬ p331) ∨ (¬ p532) ∨ (¬ p381)) : (¬ p532) ∨ (¬ p381) ∨ p1325 ∨ p419 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p381 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p331 := by
    exact h35686
  rcases h29772 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)

theorem step36175 (p15 p234 p344 p419 p1055 p1076 p1103 : Prop)
    (h35504 : p1103)
    (h29777 : (¬ p1055) ∨ p419 ∨ (¬ p15) ∨ p344 ∨ (¬ p1103) ∨ (¬ p234) ∨ p1076) : (¬ p1055) ∨ (¬ p15) ∨ p419 ∨ p344 ∨ (¬ p234) ∨ p1076 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1103 := by
    exact h35504
  rcases h29777 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)

theorem step36176 (p15 p16 p185 p234 p419 p1115 : Prop)
    (h35539 : p16)
    (h29780 : (¬ p1115) ∨ p419 ∨ (¬ p185) ∨ (¬ p234) ∨ (¬ p15) ∨ (¬ p16)) : (¬ p1115) ∨ (¬ p185) ∨ p419 ∨ (¬ p234) ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p16 := by
    exact h35539
  rcases h29780 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)

theorem step36177 (p2 p419 p985 p1096 p1325 p1538 : Prop)
    (h35503 : p985)
    (h29794 : (¬ p1538) ∨ p419 ∨ p2 ∨ p1325 ∨ (¬ p985) ∨ p1096) : (¬ p1538) ∨ p2 ∨ p419 ∨ p1325 ∨ p1096 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1538 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p2) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p985 := by
    exact h35503
  rcases h29794 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u5)
  · exact False.elim (u4 q5)

theorem step36178 (p8 p39 p63 p68 p419 p540 p561 p1325 p1431 p1667 : Prop)
    (h35495 : p39)
    (h29796 : (¬ p1431) ∨ (¬ p1667) ∨ (¬ p8) ∨ (¬ p68) ∨ (¬ p39) ∨ (¬ p540) ∨ p419 ∨ (¬ p63) ∨ p1325 ∨ (¬ p561)) : (¬ p1431) ∨ (¬ p1667) ∨ (¬ p8) ∨ (¬ p68) ∨ (¬ p540) ∨ p419 ∨ (¬ p63) ∨ p1325 ∨ (¬ p561) := by
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
  have u2 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p540 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p39 := by
    exact h35495
  rcases h29796 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u6)
  · exact False.elim (u7 q8)
  · exact False.elim (q9 u8)

theorem step36179 (p2 p39 p68 p88 p185 p419 p985 p1325 p1584 : Prop)
    (h35503 : p985)
    (h35495 : p39)
    (h29805 : (¬ p1584) ∨ p419 ∨ (¬ p68) ∨ p1325 ∨ (¬ p985) ∨ (¬ p39) ∨ (¬ p185) ∨ (¬ p88) ∨ p2) : (¬ p1584) ∨ (¬ p68) ∨ p419 ∨ p1325 ∨ (¬ p185) ∨ (¬ p88) ∨ p2 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p985 := by
    exact h35503
  have u8 : p39 := by
    exact h35495
  rcases h29805 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (u6 q8)

theorem step36180 (p15 p16 p185 p423 p985 p1035 p1584 : Prop)
    (h35539 : p16)
    (h35503 : p985)
    (h17721 : (¬ p15) ∨ (¬ p16) ∨ (¬ p185) ∨ (¬ p423) ∨ (¬ p985) ∨ (¬ p1035) ∨ (¬ p1584)) : (¬ p423) ∨ (¬ p1584) ∨ (¬ p1035) ∨ (¬ p15) ∨ (¬ p185) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p16 := by
    exact h35539
  have u6 : p985 := by
    exact h35503
  rcases h17721 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u1)

theorem step36181 (p10 p63 p364 p382 p918 p985 p1325 p1584 : Prop)
    (h35503 : p985)
    (h29808 : p382 ∨ (¬ p364) ∨ (¬ p918) ∨ p63 ∨ (¬ p1584) ∨ p10 ∨ p1325 ∨ (¬ p985)) : (¬ p918) ∨ p382 ∨ (¬ p364) ∨ p63 ∨ (¬ p1584) ∨ p10 ∨ p1325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p364 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p985 := by
    exact h35503
  rcases h29808 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (u5 q5)
  · exact False.elim (u6 q6)
  · exact False.elim (q7 u7)

theorem step36182 (p124 p267 p726 p789 p790 p985 p1325 : Prop)
    (h35503 : p985)
    (h29809 : (¬ p789) ∨ p1325 ∨ (¬ p267) ∨ p124 ∨ (¬ p985) ∨ (¬ p790) ∨ (¬ p726)) : (¬ p267) ∨ p124 ∨ p1325 ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p726) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p267 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p985 := by
    exact h35503
  rcases h29809 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step36183 (p16 p185 p455 p495 p985 p1452 p1584 : Prop)
    (h35539 : p16)
    (h35503 : p985)
    (h29810 : (¬ p1584) ∨ (¬ p1452) ∨ p495 ∨ (¬ p16) ∨ (¬ p185) ∨ (¬ p455) ∨ (¬ p985)) : (¬ p1452) ∨ (¬ p1584) ∨ p495 ∨ (¬ p185) ∨ (¬ p455) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p16 := by
    exact h35539
  have u6 : p985 := by
    exact h35503
  rcases h29810 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u6)

theorem step36184 (p16 p125 p185 p303 p498 p985 p1325 p1584 : Prop)
    (h35503 : p985)
    (h35539 : p16)
    (h29811 : (¬ p1584) ∨ p303 ∨ p1325 ∨ (¬ p985) ∨ (¬ p498) ∨ (¬ p185) ∨ p125 ∨ (¬ p16)) : p303 ∨ (¬ p1584) ∨ p1325 ∨ (¬ p498) ∨ (¬ p185) ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p985 := by
    exact h35503
  have u7 : p16 := by
    exact h35539
  rcases h29811 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u7)

theorem step36185 (p382 p495 p617 p633 p726 p985 p1325 : Prop)
    (h35503 : p985)
    (h29812 : p382 ∨ p1325 ∨ (¬ p495) ∨ (¬ p617) ∨ (¬ p726) ∨ (¬ p985) ∨ p633) : p382 ∨ (¬ p495) ∨ p1325 ∨ (¬ p617) ∨ (¬ p726) ∨ p633 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p617 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p633) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p985 := by
    exact h35503
  rcases h29812 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)
  · exact False.elim (u5 q6)

theorem step36186 (p63 p918 p985 p1035 p1140 p1584 : Prop)
    (h35503 : p985)
    (h29813 : (¬ p1584) ∨ (¬ p1035) ∨ p63 ∨ (¬ p985) ∨ (¬ p1140) ∨ (¬ p918)) : (¬ p1584) ∨ p63 ∨ (¬ p1035) ∨ (¬ p1140) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p63) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p985 := by
    exact h35503
  rcases h29813 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step36187 (p63 p234 p382 p476 p918 p985 p1325 p1584 : Prop)
    (h35503 : p985)
    (h29814 : (¬ p1584) ∨ (¬ p476) ∨ (¬ p918) ∨ p63 ∨ (¬ p985) ∨ p382 ∨ p1325 ∨ (¬ p234)) : (¬ p1584) ∨ (¬ p476) ∨ (¬ p918) ∨ p63 ∨ p382 ∨ p1325 ∨ (¬ p234) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p476 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p985 := by
    exact h35503
  rcases h29814 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u7)
  · exact False.elim (u4 q5)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u6)

theorem step36238 (p84 p224 p495 p582 p595 p789 p790 p906 : Prop)
    (h35574 : p582)
    (h29857 : (¬ p906) ∨ (¬ p789) ∨ (¬ p790) ∨ p495 ∨ (¬ p84) ∨ (¬ p224) ∨ (¬ p582) ∨ p595) : (¬ p906) ∨ (¬ p789) ∨ (¬ p790) ∨ p495 ∨ (¬ p84) ∨ (¬ p224) ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p906 := by
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
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p582 := by
    exact h35574
  rcases h29857 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u7)
  · exact False.elim (u6 q7)

theorem step36239 (p16 p189 p224 p424 p545 p903 p1096 p1286 : Prop)
    (h35539 : p16)
    (h29887 : p424 ∨ (¬ p189) ∨ (¬ p16) ∨ (¬ p1286) ∨ (¬ p1096) ∨ (¬ p224) ∨ (¬ p545) ∨ (¬ p903)) : p424 ∨ (¬ p189) ∨ (¬ p1286) ∨ (¬ p1096) ∨ (¬ p224) ∨ (¬ p545) ∨ (¬ p903) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p903 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p16 := by
    exact h35539
  rcases h29887 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step36240 (p16 p163 p189 p225 p382 p620 p901 p1287 : Prop)
    (h35539 : p16)
    (h29888 : p382 ∨ p163 ∨ (¬ p225) ∨ (¬ p620) ∨ (¬ p16) ∨ (¬ p1287) ∨ (¬ p901) ∨ (¬ p189)) : p382 ∨ p163 ∨ (¬ p225) ∨ (¬ p620) ∨ (¬ p1287) ∨ (¬ p901) ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
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
  have u5 : p901 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p16 := by
    exact h35539
  rcases h29888 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step36241 (p6 p68 p121 p885 p985 p1096 p1452 p1567 p1667 : Prop)
    (h35503 : p985)
    (h29894 : (¬ p1567) ∨ (¬ p1667) ∨ (¬ p68) ∨ p6 ∨ (¬ p985) ∨ (¬ p121) ∨ (¬ p1096) ∨ (¬ p1452) ∨ (¬ p885)) : (¬ p1567) ∨ (¬ p1667) ∨ (¬ p68) ∨ p6 ∨ (¬ p121) ∨ (¬ p1096) ∨ (¬ p1452) ∨ (¬ p885) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1567 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1667 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p121 := by
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
  have u7 : p885 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p985 := by
    exact h35503
  rcases h29894 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step36243 (p16 p134 p189 p234 p310 p330 p498 p879 p1055 p1074 : Prop)
    (h35499 : p330)
    (h35539 : p16)
    (h29939 : (¬ p1074) ∨ p1055 ∨ (¬ p498) ∨ (¬ p189) ∨ (¬ p330) ∨ (¬ p16) ∨ (¬ p134) ∨ (¬ p234) ∨ (¬ p879) ∨ (¬ p310)) : (¬ p1074) ∨ p1055 ∨ (¬ p498) ∨ (¬ p189) ∨ (¬ p134) ∨ (¬ p234) ∨ (¬ p879) ∨ (¬ p310) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p879 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p330 := by
    exact h35499
  have u9 : p16 := by
    exact h35539
  rcases h29939 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)

theorem step36244 (p41 p83 p124 p189 p344 p496 p842 p1385 : Prop)
    (h35500 : p496)
    (h19826 : (¬ p41) ∨ (¬ p83) ∨ (¬ p124) ∨ (¬ p189) ∨ (¬ p344) ∨ (¬ p496) ∨ (¬ p842) ∨ (¬ p1385)) : (¬ p344) ∨ (¬ p124) ∨ (¬ p189) ∨ (¬ p842) ∨ (¬ p1385) ∨ (¬ p83) ∨ (¬ p41) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
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
  have u3 : p842 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p496 := by
    exact h35500
  rcases h19826 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step36246 (p185 p664 p790 p833 p1115 : Prop)
    (h35502 : p664)
    (h19854 : (¬ p185) ∨ (¬ p664) ∨ (¬ p790) ∨ (¬ p833) ∨ (¬ p1115)) : (¬ p1115) ∨ (¬ p790) ∨ (¬ p185) ∨ (¬ p833) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p833 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p664 := by
    exact h35502
  rcases h19854 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u0)

theorem step36247 (p6 p121 p156 p185 p192 p224 p389 p790 p833 : Prop)
    (h35659 : p156)
    (h29984 : (¬ p389) ∨ p121 ∨ (¬ p192) ∨ (¬ p6) ∨ (¬ p833) ∨ p224 ∨ (¬ p185) ∨ (¬ p156) ∨ (¬ p790)) : (¬ p389) ∨ (¬ p192) ∨ p121 ∨ (¬ p6) ∨ (¬ p833) ∨ p224 ∨ (¬ p185) ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p121) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p833 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p156 := by
    exact h35659
  rcases h29984 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u7)

theorem step36249 (p163 p189 p382 p533 p534 p821 p1325 : Prop)
    (h35501 : p533)
    (h29989 : (¬ p534) ∨ p189 ∨ (¬ p382) ∨ (¬ p821) ∨ (¬ p163) ∨ (¬ p1325) ∨ (¬ p533)) : (¬ p534) ∨ (¬ p382) ∨ p189 ∨ (¬ p821) ∨ (¬ p163) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p821 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p533 := by
    exact h35501
  rcases h29989 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)

theorem step36251 (p163 p189 p382 p817 p940 p985 p1325 : Prop)
    (h35503 : p985)
    (h29993 : p382 ∨ (¬ p940) ∨ p1325 ∨ p163 ∨ (¬ p817) ∨ (¬ p189) ∨ (¬ p985)) : (¬ p940) ∨ p382 ∨ p1325 ∨ p163 ∨ (¬ p817) ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p817 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p985 := by
    exact h35503
  rcases h29993 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u2 q2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)

theorem step36252 (p6 p101 p188 p382 p726 p817 p985 p1325 : Prop)
    (h35503 : p985)
    (h30020 : p382 ∨ p1325 ∨ (¬ p101) ∨ (¬ p985) ∨ (¬ p6) ∨ (¬ p188) ∨ (¬ p817) ∨ (¬ p726)) : p382 ∨ p1325 ∨ (¬ p101) ∨ (¬ p6) ∨ (¬ p188) ∨ (¬ p817) ∨ (¬ p726) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p817 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p985 := by
    exact h35503
  rcases h30020 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step36254 (p156 p189 p435 p790 p798 p980 p1115 p1335 : Prop)
    (h35659 : p156)
    (h30034 : p790 ∨ (¬ p798) ∨ p189 ∨ (¬ p156) ∨ (¬ p1335) ∨ p1115 ∨ p980 ∨ (¬ p435)) : (¬ p798) ∨ p790 ∨ p189 ∨ (¬ p1335) ∨ p1115 ∨ p980 ∨ (¬ p435) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p798 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p790) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p156 := by
    exact h35659
  rcases h30034 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u3)
  · exact False.elim (u4 q5)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u6)

theorem step36255 (p533 p754 p1449 : Prop)
    (h35501 : p533)
    (h12932 : (¬ p533) ∨ (¬ p754) ∨ p1449) : (¬ p754) ∨ p1449 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p754 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1449) := fun hu => hn (Or.inr hu)
  have u2 : p533 := by
    exact h35501
  rcases h12932 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (u1 q2)

theorem step36256 (p124 p189 p258 p422 p751 p985 p1035 p1624 : Prop)
    (h35503 : p985)
    (h30042 : (¬ p1624) ∨ (¬ p1035) ∨ (¬ p985) ∨ (¬ p258) ∨ (¬ p124) ∨ (¬ p751) ∨ p189 ∨ p422) : (¬ p751) ∨ (¬ p1624) ∨ (¬ p258) ∨ (¬ p124) ∨ (¬ p1035) ∨ p189 ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p751 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1624 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p985 := by
    exact h35503
  rcases h30042 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u0)
  · exact False.elim (u5 q6)
  · exact False.elim (u6 q7)

theorem step36259 (p41 p156 p158 p382 p680 p1287 p1387 : Prop)
    (h35659 : p156)
    (h30070 : p382 ∨ (¬ p41) ∨ (¬ p158) ∨ (¬ p1387) ∨ (¬ p1287) ∨ (¬ p156) ∨ (¬ p680)) : p382 ∨ (¬ p158) ∨ (¬ p41) ∨ (¬ p1387) ∨ (¬ p1287) ∨ (¬ p680) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p41 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p156 := by
    exact h35659
  rcases h30070 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u5)

theorem step36260 (p12 p83 p160 p163 p189 p1233 p1325 : Prop)
    (h35505 : p1233)
    (h30077 : (¬ p160) ∨ p163 ∨ p12 ∨ (¬ p189) ∨ (¬ p83) ∨ (¬ p1233) ∨ (¬ p1325)) : (¬ p160) ∨ p163 ∨ p12 ∨ (¬ p189) ∨ (¬ p83) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1233 := by
    exact h35505
  rcases h30077 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u5)

theorem step36261 (p12 p87 p163 p189 p382 p816 p1385 : Prop)
    (h35497 : p87)
    (h30079 : p12 ∨ p163 ∨ p1385 ∨ (¬ p87) ∨ (¬ p816) ∨ (¬ p189) ∨ p382) : p1385 ∨ p163 ∨ p12 ∨ (¬ p816) ∨ (¬ p189) ∨ p382 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1385) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p816 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p87 := by
    exact h35497
  rcases h30079 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)

theorem step36262 (p16 p71 p185 p1035 p1115 p1140 p1325 : Prop)
    (h35539 : p16)
    (h25956 : (¬ p1325) ∨ (¬ p1035) ∨ (¬ p1115) ∨ (¬ p16) ∨ (¬ p185) ∨ (¬ p71) ∨ (¬ p1140)) : (¬ p1140) ∨ (¬ p71) ∨ (¬ p185) ∨ (¬ p1035) ∨ (¬ p1325) ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1140 := by
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
  have u3 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p16 := by
    exact h35539
  rcases h25956 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u0)

theorem step36263 (p12 p14 p47 p87 p189 p382 p816 p1385 : Prop)
    (h35497 : p87)
    (h30081 : p14 ∨ p1385 ∨ (¬ p47) ∨ (¬ p87) ∨ p12 ∨ (¬ p816) ∨ p382 ∨ (¬ p189)) : p1385 ∨ p14 ∨ (¬ p47) ∨ p12 ∨ (¬ p816) ∨ p382 ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1385) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p14) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p816 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p87 := by
    exact h35497
  rcases h30081 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u7)
  · exact False.elim (u3 q4)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u6)

theorem step36264 (p12 p14 p15 p86 p789 p790 : Prop)
    (h35496 : p86)
    (h30082 : p14 ∨ p12 ∨ p15 ∨ (¬ p789) ∨ (¬ p86) ∨ (¬ p790)) : p14 ∨ p15 ∨ p12 ∨ (¬ p789) ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p86 := by
    exact h35496
  rcases h30082 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u4)

theorem step36265 (p17 p86 p126 p303 p1074 p1096 : Prop)
    (h35496 : p86)
    (h30083 : p303 ∨ p17 ∨ (¬ p126) ∨ p1096 ∨ (¬ p86) ∨ (¬ p1074)) : p303 ∨ (¬ p126) ∨ p17 ∨ p1096 ∨ (¬ p1074) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p86 := by
    exact h35496
  rcases h30083 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u4)

theorem step36266 (p63 p125 p303 p496 p918 p1115 : Prop)
    (h35500 : p496)
    (h30085 : (¬ p918) ∨ (¬ p1115) ∨ (¬ p496) ∨ p63 ∨ p303 ∨ p125) : (¬ p1115) ∨ (¬ p918) ∨ p63 ∨ p303 ∨ p125 := by
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
  have u3 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p496 := by
    exact h35500
  rcases h30085 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (u2 q3)
  · exact False.elim (u3 q4)
  · exact False.elim (u4 q5)

theorem step36267 (p12 p14 p15 p125 p303 p496 : Prop)
    (h35500 : p496)
    (h30086 : p14 ∨ p12 ∨ p125 ∨ (¬ p496) ∨ p15 ∨ p303) : p14 ∨ p12 ∨ p125 ∨ p15 ∨ p303 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p496 := by
    exact h35500
  rcases h30086 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u5)
  · exact False.elim (u3 q4)
  · exact False.elim (u4 q5)

theorem step36268 (p86 p495 p633 p789 p790 p1076 : Prop)
    (h35496 : p86)
    (h30088 : (¬ p789) ∨ p633 ∨ (¬ p790) ∨ (¬ p1076) ∨ (¬ p86) ∨ (¬ p495)) : (¬ p790) ∨ p633 ∨ (¬ p789) ∨ (¬ p1076) ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p633) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p86 := by
    exact h35496
  rcases h30088 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u4)

theorem step36269 (p39 p63 p234 p419 p923 p1096 p1115 : Prop)
    (h35495 : p39)
    (h30091 : (¬ p1115) ∨ p419 ∨ p1096 ∨ (¬ p63) ∨ (¬ p923) ∨ (¬ p39) ∨ (¬ p234)) : (¬ p1115) ∨ (¬ p63) ∨ p419 ∨ p1096 ∨ (¬ p923) ∨ (¬ p234) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p923 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p39 := by
    exact h35495
  rcases h30091 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (u3 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u5)

theorem step36270 (p63 p124 p425 p582 p595 p1076 p1286 : Prop)
    (h35574 : p582)
    (h30092 : (¬ p425) ∨ p124 ∨ (¬ p1076) ∨ (¬ p1286) ∨ (¬ p582) ∨ (¬ p595) ∨ p63) : p124 ∨ (¬ p425) ∨ (¬ p1076) ∨ (¬ p1286) ∨ (¬ p595) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p582 := by
    exact h35574
  rcases h30092 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)

theorem step36271 (p12 p16 p163 p189 p595 p1286 : Prop)
    (h35539 : p16)
    (h30094 : p12 ∨ p163 ∨ (¬ p189) ∨ (¬ p1286) ∨ (¬ p595) ∨ (¬ p16)) : p163 ∨ p12 ∨ (¬ p189) ∨ (¬ p1286) ∨ (¬ p595) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p163) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p16 := by
    exact h35539
  rcases h30094 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)

theorem step36272 (p6 p10 p39 p68 p88 p185 p303 p1115 : Prop)
    (h35495 : p39)
    (h30098 : p303 ∨ (¬ p1115) ∨ (¬ p68) ∨ (¬ p88) ∨ (¬ p185) ∨ p10 ∨ p6 ∨ (¬ p39)) : (¬ p1115) ∨ p303 ∨ (¬ p68) ∨ (¬ p88) ∨ (¬ p185) ∨ p10 ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p39 := by
    exact h35495
  rcases h30098 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (u5 q5)
  · exact False.elim (u6 q6)
  · exact False.elim (q7 u7)

theorem step36273 (p4 p126 p258 p668 p1076 : Prop)
    (h35527 : p668)
    (h30099 : p126 ∨ (¬ p4) ∨ p258 ∨ (¬ p668) ∨ p1076) : p258 ∨ p126 ∨ (¬ p4) ∨ p1076 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p258) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p668 := by
    exact h35527
  rcases h30099 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (u3 q4)

theorem step36275 (p3 p5 p63 p225 p668 p918 p1115 : Prop)
    (h35527 : p668)
    (h30101 : p3 ∨ p918 ∨ p1115 ∨ (¬ p63) ∨ (¬ p225) ∨ (¬ p668) ∨ (¬ p5)) : p918 ∨ p3 ∨ p1115 ∨ (¬ p63) ∨ (¬ p225) ∨ (¬ p5) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p918) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p668 := by
    exact h35527
  rcases h30101 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u5)

theorem step36276 (p14 p47 p87 p189 p225 p668 p918 p1115 : Prop)
    (h35497 : p87)
    (h35527 : p668)
    (h30102 : p14 ∨ p918 ∨ (¬ p87) ∨ (¬ p668) ∨ p1115 ∨ (¬ p47) ∨ (¬ p225) ∨ (¬ p189)) : p14 ∨ p918 ∨ p1115 ∨ (¬ p47) ∨ (¬ p225) ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p87 := by
    exact h35497
  have u7 : p668 := by
    exact h35527
  rcases h30102 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (u2 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)

theorem step36278 (p3 p225 p668 p1041 p1140 : Prop)
    (h35527 : p668)
    (h30104 : p3 ∨ (¬ p225) ∨ (¬ p1140) ∨ (¬ p1041) ∨ (¬ p668)) : (¬ p1140) ∨ (¬ p1041) ∨ (¬ p225) ∨ p3 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1041 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p668 := by
    exact h35527
  rcases h30104 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)

theorem step36279 (p163 p225 p422 p668 p1041 : Prop)
    (h35527 : p668)
    (h30105 : p163 ∨ (¬ p225) ∨ p422 ∨ (¬ p668) ∨ (¬ p1041)) : p163 ∨ p422 ∨ (¬ p225) ∨ (¬ p1041) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p163) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p422) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1041 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p668 := by
    exact h35527
  rcases h30105 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)

theorem step36280 (p8 p303 p347 p666 p1055 : Prop)
    (h35646 : p347)
    (h30117 : p1055 ∨ (¬ p347) ∨ (¬ p303) ∨ p8 ∨ (¬ p666)) : p1055 ∨ (¬ p303) ∨ p8 ∨ (¬ p666) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1055) := fun hu => hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p666 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p347 := by
    exact h35646
  rcases h30117 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (u2 q3)
  · exact False.elim (q4 u3)

theorem step36281 (p8 p12 p303 p347 p560 p666 : Prop)
    (h35646 : p347)
    (h30120 : (¬ p560) ∨ (¬ p12) ∨ (¬ p347) ∨ (¬ p666) ∨ (¬ p303) ∨ p8) : (¬ p12) ∨ p8 ∨ (¬ p666) ∨ (¬ p303) ∨ (¬ p560) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p8) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p666 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p347 := by
    exact h35646
  rcases h30120 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u1 q5)

theorem step36282 (p8 p9 p16 p101 p134 p189 p638 p897 : Prop)
    (h35539 : p16)
    (h18483 : (¬ p8) ∨ (¬ p9) ∨ (¬ p16) ∨ (¬ p101) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p638) ∨ (¬ p897)) : (¬ p897) ∨ (¬ p134) ∨ (¬ p9) ∨ (¬ p189) ∨ (¬ p101) ∨ (¬ p638) ∨ (¬ p8) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p9 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p638 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p16 := by
    exact h35539
  rcases h18483 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u0)

theorem step36283 (p16 p160 p161 p185 p344 p638 p836 p1236 p1306 : Prop)
    (h35539 : p16)
    (h20125 : (¬ p16) ∨ (¬ p160) ∨ (¬ p161) ∨ (¬ p185) ∨ (¬ p344) ∨ (¬ p638) ∨ (¬ p836) ∨ (¬ p1236) ∨ (¬ p1306)) : (¬ p836) ∨ (¬ p344) ∨ (¬ p638) ∨ (¬ p160) ∨ (¬ p1236) ∨ (¬ p1306) ∨ (¬ p161) ∨ (¬ p185) := by
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
  have u2 : p638 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1236 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p16 := by
    exact h35539
  rcases h20125 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)

theorem step36284 (p6 p14 p24 p67 p225 p633 p664 p1076 : Prop)
    (h35502 : p664)
    (h30131 : p633 ∨ (¬ p1076) ∨ (¬ p14) ∨ (¬ p67) ∨ (¬ p6) ∨ p225 ∨ (¬ p24) ∨ (¬ p664)) : p633 ∨ (¬ p6) ∨ (¬ p14) ∨ (¬ p67) ∨ (¬ p1076) ∨ p225 ∨ (¬ p24) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p664 := by
    exact h35502
  rcases h30131 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u7)

theorem step36285 (p86 p185 p344 p495 p633 p668 p1115 : Prop)
    (h35496 : p86)
    (h35527 : p668)
    (h30137 : p633 ∨ p185 ∨ (¬ p86) ∨ (¬ p495) ∨ p1115 ∨ (¬ p668) ∨ p344) : p633 ∨ p185 ∨ (¬ p495) ∨ p1115 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p86 := by
    exact h35496
  have u6 : p668 := by
    exact h35527
  rcases h30137 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (u3 q4)
  · exact False.elim (q5 u6)
  · exact False.elim (u4 q6)

theorem step36286 (p63 p124 p498 p582 p633 : Prop)
    (h35574 : p582)
    (h30145 : p633 ∨ (¬ p124) ∨ p63 ∨ (¬ p582) ∨ (¬ p498)) : p633 ∨ p63 ∨ (¬ p124) ∨ (¬ p498) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p63) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p582 := by
    exact h35574
  rcases h30145 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)

theorem step36287 (p20 p124 p207 p234 p330 p633 : Prop)
    (h35499 : p330)
    (h30147 : (¬ p124) ∨ p633 ∨ (¬ p330) ∨ (¬ p207) ∨ (¬ p234) ∨ (¬ p20)) : p633 ∨ (¬ p207) ∨ (¬ p124) ∨ (¬ p234) ∨ (¬ p20) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p20 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p330 := by
    exact h35499
  rcases h30147 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step36288 (p16 p124 p228 p455 p498 p633 p789 p790 : Prop)
    (h35539 : p16)
    (h30149 : (¬ p124) ∨ (¬ p455) ∨ (¬ p16) ∨ (¬ p498) ∨ p790 ∨ p633 ∨ p789 ∨ (¬ p228)) : p633 ∨ (¬ p455) ∨ (¬ p498) ∨ p790 ∨ (¬ p124) ∨ p789 ∨ (¬ p228) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p16 := by
    exact h35539
  rcases h30149 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u2)
  · exact False.elim (u3 q4)
  · exact False.elim (u0 q5)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u6)

theorem step36289 (p348 p420 p633 p664 p1076 : Prop)
    (h35502 : p664)
    (h30158 : p633 ∨ (¬ p348) ∨ p420 ∨ (¬ p1076) ∨ (¬ p664)) : p420 ∨ (¬ p348) ∨ p633 ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p420) := fun hu => hn (Or.inl hu)
  have u1 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p633) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p664 := by
    exact h35502
  rcases h30158 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)

theorem step36290 (p41 p138 p258 p575 p633 : Prop)
    (h35668 : p138)
    (h30160 : (¬ p575) ∨ p258 ∨ (¬ p41) ∨ p633 ∨ (¬ p138)) : p258 ∨ (¬ p575) ∨ (¬ p41) ∨ p633 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p258) := fun hu => hn (Or.inl hu)
  have u1 : p575 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p633) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p138 := by
    exact h35668
  rcases h30160 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)

theorem step36291 (p41 p158 p344 p495 p633 p668 p918 p1055 : Prop)
    (h35527 : p668)
    (h30163 : p633 ∨ p918 ∨ (¬ p495) ∨ p344 ∨ (¬ p668) ∨ p41 ∨ p1055 ∨ (¬ p158)) : p633 ∨ p918 ∨ (¬ p495) ∨ p344 ∨ p41 ∨ p1055 ∨ (¬ p158) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p668 := by
    exact h35527
  rcases h30163 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u7)
  · exact False.elim (u4 q5)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u6)

theorem step36292 (p3 p225 p495 p633 p664 p1076 : Prop)
    (h35502 : p664)
    (h30164 : (¬ p3) ∨ p633 ∨ (¬ p495) ∨ p225 ∨ (¬ p664) ∨ (¬ p1076)) : p633 ∨ (¬ p495) ∨ (¬ p3) ∨ p225 ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p664 := by
    exact h35502
  rcases h30164 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u4)

theorem step36294 (p382 p495 p533 p621 p633 p756 p1325 : Prop)
    (h35501 : p533)
    (h30180 : (¬ p756) ∨ (¬ p633) ∨ (¬ p533) ∨ (¬ p1325) ∨ (¬ p621) ∨ p495 ∨ (¬ p382)) : (¬ p756) ∨ (¬ p633) ∨ (¬ p1325) ∨ (¬ p621) ∨ p495 ∨ (¬ p382) := by
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
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p621 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p533 := by
    exact h35501
  rcases h30180 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u4 q5)
  · exact False.elim (q6 u5)

theorem step36298 (p63 p124 p421 p577 p668 p897 p1076 p1096 : Prop)
    (h35527 : p668)
    (h30202 : p1096 ∨ p1076 ∨ (¬ p421) ∨ (¬ p897) ∨ (¬ p124) ∨ (¬ p577) ∨ (¬ p668) ∨ (¬ p63)) : p1096 ∨ (¬ p897) ∨ (¬ p421) ∨ p1076 ∨ (¬ p124) ∨ (¬ p577) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1096) := fun hu => hn (Or.inl hu)
  have u1 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p124 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p668 := by
    exact h35527
  rcases h30202 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u0 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u6)

theorem step36299 (p15 p39 p498 p575 p1604 p1631 : Prop)
    (h35495 : p39)
    (h30235 : (¬ p1604) ∨ (¬ p1631) ∨ (¬ p575) ∨ (¬ p498) ∨ p15 ∨ (¬ p39)) : (¬ p1631) ∨ (¬ p1604) ∨ (¬ p575) ∨ (¬ p498) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1631 := by
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
  have u3 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p39 := by
    exact h35495
  rcases h30235 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u5)

theorem step36300 (p41 p125 p138 p262 p420 p575 : Prop)
    (h35668 : p138)
    (h30236 : (¬ p420) ∨ (¬ p41) ∨ (¬ p262) ∨ (¬ p138) ∨ (¬ p575) ∨ p125) : (¬ p420) ∨ p125 ∨ (¬ p262) ∨ (¬ p575) ∨ (¬ p41) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p125) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p575 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p138 := by
    exact h35668
  rcases h30236 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (u1 q5)

theorem step36301 (p15 p39 p125 p126 p225 p258 p425 p575 p883 p1096 : Prop)
    (h35495 : p39)
    (h30238 : (¬ p125) ∨ (¬ p425) ∨ p225 ∨ (¬ p883) ∨ p15 ∨ (¬ p575) ∨ (¬ p126) ∨ (¬ p39) ∨ (¬ p1096) ∨ (¬ p258)) : (¬ p126) ∨ (¬ p125) ∨ p225 ∨ (¬ p883) ∨ p15 ∨ (¬ p575) ∨ (¬ p425) ∨ (¬ p1096) ∨ (¬ p258) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p883 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p575 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p39 := by
    exact h35495
  rcases h30238 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u6)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step36302 (p15 p39 p425 p532 p575 p961 p1229 p1291 p1325 : Prop)
    (h35495 : p39)
    (h30239 : (¬ p961) ∨ (¬ p1229) ∨ (¬ p1291) ∨ (¬ p532) ∨ (¬ p575) ∨ (¬ p425) ∨ (¬ p39) ∨ p1325 ∨ p15) : (¬ p1229) ∨ (¬ p961) ∨ (¬ p1291) ∨ (¬ p532) ∨ (¬ p575) ∨ (¬ p425) ∨ p1325 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1291 := by
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
  have u5 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p39 := by
    exact h35495
  rcases h30239 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u8)
  · exact False.elim (u6 q7)
  · exact False.elim (u7 q8)

theorem step36304 (p15 p39 p227 p455 p498 p575 : Prop)
    (h35495 : p39)
    (h30242 : p455 ∨ (¬ p498) ∨ (¬ p575) ∨ (¬ p227) ∨ (¬ p39) ∨ p15) : p455 ∨ (¬ p575) ∨ (¬ p498) ∨ (¬ p227) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : p575 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p39 := by
    exact h35495
  rcases h30242 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)
  · exact False.elim (u4 q5)

theorem step36305 (p39 p63 p68 p561 p864 p980 p1055 p1229 p1269 p1325 : Prop)
    (h35495 : p39)
    (h30248 : (¬ p864) ∨ p980 ∨ p1055 ∨ (¬ p68) ∨ p1229 ∨ (¬ p1325) ∨ (¬ p561) ∨ (¬ p63) ∨ (¬ p39) ∨ (¬ p1269)) : (¬ p864) ∨ p1055 ∨ p980 ∨ (¬ p68) ∨ p1229 ∨ (¬ p1325) ∨ (¬ p561) ∨ (¬ p63) ∨ (¬ p1269) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p864 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1269 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p39 := by
    exact h35495
  rcases h30248 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u9)
  · exact False.elim (q9 u8)

theorem step36306 (p163 p195 p536 p561 p940 : Prop)
    (h35556 : p195)
    (h30250 : (¬ p940) ∨ (¬ p536) ∨ (¬ p195) ∨ p163 ∨ (¬ p561)) : (¬ p536) ∨ (¬ p940) ∨ p163 ∨ (¬ p561) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p536 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p195 := by
    exact h35556
  rcases h30250 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (u2 q3)
  · exact False.elim (q4 u3)

theorem step36307 (p12 p39 p63 p68 p225 p351 p561 p595 p597 p1055 : Prop)
    (h35495 : p39)
    (h30255 : (¬ p597) ∨ p595 ∨ p1055 ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p39) ∨ (¬ p561) ∨ p225 ∨ (¬ p351) ∨ p12) : (¬ p597) ∨ p1055 ∨ p595 ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p561) ∨ p225 ∨ (¬ p351) ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p597 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p39 := by
    exact h35495
  rcases h30255 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u5)
  · exact False.elim (u6 q7)
  · exact False.elim (q8 u7)
  · exact False.elim (u8 q9)

theorem step36309 (p8 p138 p192 p556 p576 p897 p927 : Prop)
    (h35668 : p138)
    (h30288 : (¬ p556) ∨ (¬ p927) ∨ (¬ p192) ∨ (¬ p138) ∨ (¬ p576) ∨ p8 ∨ p897) : (¬ p927) ∨ (¬ p192) ∨ (¬ p556) ∨ (¬ p576) ∨ p8 ∨ p897 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p927 := by
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
  have u4 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p138 := by
    exact h35668
  rcases h30288 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (u4 q5)
  · exact False.elim (u5 q6)

theorem step36311 (p17 p138 p192 p225 p534 p556 p769 p790 p838 : Prop)
    (h35668 : p138)
    (h18965 : (¬ p17) ∨ (¬ p138) ∨ (¬ p192) ∨ (¬ p225) ∨ (¬ p534) ∨ (¬ p556) ∨ (¬ p769) ∨ (¬ p790) ∨ (¬ p838)) : (¬ p534) ∨ (¬ p769) ∨ (¬ p556) ∨ (¬ p225) ∨ (¬ p192) ∨ (¬ p790) ∨ (¬ p838) ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p769 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p556 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p838 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p138 := by
    exact h35668
  rcases h18965 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)

theorem step36312 (p2 p12 p108 p330 p556 p1055 : Prop)
    (h35499 : p330)
    (h30304 : (¬ p556) ∨ (¬ p1055) ∨ (¬ p12) ∨ (¬ p108) ∨ p2 ∨ (¬ p330)) : (¬ p12) ∨ (¬ p1055) ∨ (¬ p556) ∨ (¬ p108) ∨ p2 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p556 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p330 := by
    exact h35499
  rcases h30304 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u5)

theorem step36313 (p47 p87 p189 p224 p234 p545 p789 p839 p918 : Prop)
    (h35497 : p87)
    (h30312 : (¬ p789) ∨ (¬ p47) ∨ (¬ p839) ∨ (¬ p224) ∨ p234 ∨ (¬ p545) ∨ (¬ p189) ∨ p918 ∨ (¬ p87)) : (¬ p224) ∨ (¬ p789) ∨ (¬ p839) ∨ (¬ p47) ∨ p234 ∨ (¬ p545) ∨ (¬ p189) ∨ p918 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p224 := by
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
  have u3 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p234) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p87 := by
    exact h35497
  rcases h30312 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)
  · exact False.elim (u7 q7)
  · exact False.elim (q8 u8)

theorem step36315 (p8 p87 p158 p419 p545 p789 p790 p918 : Prop)
    (h35497 : p87)
    (h30315 : p419 ∨ p790 ∨ (¬ p8) ∨ (¬ p158) ∨ p789 ∨ (¬ p545) ∨ (¬ p87) ∨ p918) : p790 ∨ p419 ∨ (¬ p8) ∨ (¬ p158) ∨ p789 ∨ (¬ p545) ∨ p918 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p790) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p419) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p87 := by
    exact h35497
  rcases h30315 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u7)
  · exact False.elim (u6 q7)

theorem step36316 (p47 p87 p124 p189 p234 p262 p344 p545 p576 : Prop)
    (h35497 : p87)
    (h30316 : p234 ∨ (¬ p344) ∨ (¬ p124) ∨ (¬ p47) ∨ (¬ p87) ∨ p576 ∨ (¬ p545) ∨ (¬ p262) ∨ (¬ p189)) : (¬ p344) ∨ p234 ∨ (¬ p124) ∨ (¬ p47) ∨ p576 ∨ (¬ p545) ∨ (¬ p262) ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p234) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p87 := by
    exact h35497
  rcases h30316 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u8)
  · exact False.elim (u4 q5)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step36317 (p124 p263 p344 p419 p545 p789 p790 : Prop)
    (h35554 : p263)
    (h30317 : p419 ∨ p790 ∨ (¬ p545) ∨ (¬ p344) ∨ p789 ∨ (¬ p124) ∨ (¬ p263)) : p790 ∨ p419 ∨ (¬ p545) ∨ (¬ p344) ∨ p789 ∨ (¬ p124) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p790) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p419) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p263 := by
    exact h35554
  rcases h30317 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)

theorem step36318 (p15 p17 p86 p234 p258 p344 p545 : Prop)
    (h35496 : p86)
    (h30343 : p234 ∨ p17 ∨ (¬ p545) ∨ (¬ p86) ∨ (¬ p344) ∨ p15 ∨ p258) : p17 ∨ p234 ∨ (¬ p545) ∨ (¬ p344) ∨ p15 ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p17) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p234) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p86 := by
    exact h35496
  rcases h30343 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (u4 q5)
  · exact False.elim (u5 q6)

theorem step36319 (p15 p125 p224 p234 p303 p496 p545 : Prop)
    (h35500 : p496)
    (h30344 : p234 ∨ p303 ∨ p15 ∨ (¬ p545) ∨ (¬ p224) ∨ (¬ p496) ∨ p125) : p303 ∨ (¬ p224) ∨ p234 ∨ p15 ∨ (¬ p545) ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p234) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p496 := by
    exact h35500
  rcases h30344 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (u3 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u6)
  · exact False.elim (u5 q6)

theorem step36320 (p124 p344 p419 p496 p545 p595 p1287 : Prop)
    (h35500 : p496)
    (h30346 : p419 ∨ (¬ p545) ∨ (¬ p124) ∨ (¬ p496) ∨ (¬ p344) ∨ (¬ p1287) ∨ p595) : p419 ∨ (¬ p545) ∨ (¬ p124) ∨ (¬ p344) ∨ (¬ p1287) ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p496 := by
    exact h35500
  rcases h30346 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)

theorem step36321 (p64 p124 p234 p344 p423 p496 p545 p1140 : Prop)
    (h35500 : p496)
    (h30347 : p234 ∨ (¬ p423) ∨ (¬ p496) ∨ (¬ p124) ∨ (¬ p545) ∨ (¬ p344) ∨ (¬ p64) ∨ p1140) : (¬ p423) ∨ p234 ∨ (¬ p124) ∨ (¬ p545) ∨ (¬ p344) ∨ (¬ p64) ∨ p1140 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p234) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p496 := by
    exact h35500
  rcases h30347 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (u6 q7)

theorem step36322 (p41 p156 p537 p922 p1538 : Prop)
    (h35659 : p156)
    (h18363 : (¬ p41) ∨ (¬ p156) ∨ (¬ p537) ∨ (¬ p922) ∨ (¬ p1538)) : (¬ p537) ∨ (¬ p1538) ∨ (¬ p41) ∨ (¬ p922) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1538 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p922 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p156 := by
    exact h35659
  rcases h18363 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)

theorem step36323 (p5 p63 p533 p537 p918 p1140 p1465 : Prop)
    (h35501 : p533)
    (h30358 : (¬ p537) ∨ p1140 ∨ (¬ p5) ∨ p918 ∨ (¬ p1465) ∨ (¬ p63) ∨ (¬ p533)) : (¬ p537) ∨ p1140 ∨ (¬ p5) ∨ p918 ∨ (¬ p1465) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1140) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p533 := by
    exact h35501
  rcases h30358 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)

theorem step36324 (p87 p238 p537 p769 p918 : Prop)
    (h35497 : p87)
    (h30359 : (¬ p537) ∨ (¬ p769) ∨ (¬ p87) ∨ p918 ∨ (¬ p238)) : (¬ p537) ∨ (¬ p769) ∨ p918 ∨ (¬ p238) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p769 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p87 := by
    exact h35497
  rcases h30359 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (u2 q3)
  · exact False.elim (q4 u3)

theorem step36325 (p63 p382 p533 p537 p621 p918 p1325 : Prop)
    (h35501 : p533)
    (h30363 : (¬ p537) ∨ p918 ∨ (¬ p382) ∨ (¬ p533) ∨ (¬ p63) ∨ (¬ p621) ∨ (¬ p1325)) : (¬ p537) ∨ (¬ p382) ∨ p918 ∨ (¬ p63) ∨ (¬ p621) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p621 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p533 := by
    exact h35501
  rcases h30363 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step36326 (p86 p185 p533 p537 p595 p1287 p1325 : Prop)
    (h35501 : p533)
    (h35496 : p86)
    (h30365 : (¬ p537) ∨ p185 ∨ (¬ p1287) ∨ (¬ p533) ∨ p595 ∨ (¬ p86) ∨ (¬ p1325)) : (¬ p537) ∨ (¬ p1287) ∨ p185 ∨ p595 ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p533 := by
    exact h35501
  have u6 : p86 := by
    exact h35496
  rcases h30365 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (u3 q4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u4)

theorem step36328 (p2 p185 p194 p419 p533 p537 p1325 : Prop)
    (h35501 : p533)
    (h30367 : (¬ p537) ∨ (¬ p194) ∨ p185 ∨ (¬ p1325) ∨ (¬ p2) ∨ (¬ p419) ∨ (¬ p533)) : (¬ p537) ∨ (¬ p194) ∨ p185 ∨ (¬ p1325) ∨ (¬ p2) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p533 := by
    exact h35501
  rcases h30367 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)

theorem step36330 (p15 p86 p185 p423 p533 p537 p1465 : Prop)
    (h35496 : p86)
    (h35501 : p533)
    (h30370 : p423 ∨ (¬ p537) ∨ (¬ p86) ∨ p185 ∨ (¬ p1465) ∨ p15 ∨ (¬ p533)) : p423 ∨ (¬ p537) ∨ p185 ∨ (¬ p1465) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p86 := by
    exact h35496
  have u6 : p533 := by
    exact h35501
  rcases h30370 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (u2 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (u4 q5)
  · exact False.elim (q6 u6)

theorem step36332 (p15 p39 p88 p238 p537 p769 p1115 p1145 p1211 p1229 p1452 : Prop)
    (h35495 : p39)
    (h30374 : (¬ p769) ∨ (¬ p537) ∨ (¬ p238) ∨ (¬ p1115) ∨ (¬ p39) ∨ (¬ p1229) ∨ (¬ p1145) ∨ p15 ∨ (¬ p1211) ∨ (¬ p1452) ∨ (¬ p88)) : (¬ p537) ∨ (¬ p1452) ∨ (¬ p238) ∨ (¬ p1115) ∨ (¬ p1229) ∨ (¬ p1145) ∨ p15 ∨ (¬ p1211) ∨ (¬ p769) ∨ (¬ p88) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1145 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p769 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p39 := by
    exact h35495
  rcases h30374 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (u6 q7)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u1)
  · exact False.elim (q10 u9)

theorem step36333 (p6 p38 p49 p121 p532 p533 p537 p918 : Prop)
    (h35501 : p533)
    (h30376 : (¬ p537) ∨ p121 ∨ (¬ p532) ∨ (¬ p533) ∨ p918 ∨ (¬ p6) ∨ (¬ p38) ∨ (¬ p49)) : (¬ p537) ∨ (¬ p532) ∨ p121 ∨ p918 ∨ (¬ p6) ∨ (¬ p38) ∨ (¬ p49) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p121) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p533 := by
    exact h35501
  rcases h30376 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u7)
  · exact False.elim (u3 q4)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step36334 (p14 p15 p532 p533 p534 p961 : Prop)
    (h35501 : p533)
    (h25989 : (¬ p961) ∨ (¬ p534) ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p533) ∨ (¬ p532)) : (¬ p534) ∨ (¬ p961) ∨ (¬ p15) ∨ (¬ p532) ∨ (¬ p14) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p533 := by
    exact h35501
  rcases h25989 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u3)

theorem step36335 (p124 p496 p533 p595 p756 p1287 p1325 : Prop)
    (h35500 : p496)
    (h35501 : p533)
    (h30377 : (¬ p756) ∨ p595 ∨ (¬ p124) ∨ (¬ p496) ∨ (¬ p1325) ∨ (¬ p533) ∨ (¬ p1287)) : (¬ p756) ∨ p595 ∨ (¬ p124) ∨ (¬ p1325) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p595) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p496 := by
    exact h35500
  have u6 : p533 := by
    exact h35501
  rcases h30377 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u4)

theorem step36336 (p3 p455 p495 p532 p533 p534 : Prop)
    (h35501 : p533)
    (h30378 : (¬ p534) ∨ p455 ∨ (¬ p495) ∨ (¬ p532) ∨ (¬ p3) ∨ (¬ p533)) : (¬ p534) ∨ p455 ∨ (¬ p495) ∨ (¬ p532) ∨ (¬ p3) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p455) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p533 := by
    exact h35501
  rcases h30378 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)

theorem step36337 (p86 p185 p455 p495 p532 p533 p537 : Prop)
    (h35501 : p533)
    (h35496 : p86)
    (h30379 : (¬ p537) ∨ p455 ∨ (¬ p532) ∨ (¬ p495) ∨ p185 ∨ (¬ p533) ∨ (¬ p86)) : p455 ∨ (¬ p537) ∨ (¬ p532) ∨ (¬ p495) ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p533 := by
    exact h35501
  have u6 : p86 := by
    exact h35496
  rcases h30379 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)

theorem step36338 (p3 p190 p533 p534 p789 p790 p1325 : Prop)
    (h35501 : p533)
    (h30380 : (¬ p534) ∨ (¬ p190) ∨ p789 ∨ (¬ p1325) ∨ (¬ p533) ∨ (¬ p3) ∨ p790) : (¬ p534) ∨ (¬ p190) ∨ p789 ∨ (¬ p1325) ∨ (¬ p3) ∨ p790 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p533 := by
    exact h35501
  rcases h30380 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)

theorem step36339 (p88 p533 p577 p633 p756 p789 p790 p1325 : Prop)
    (h35501 : p533)
    (h30381 : (¬ p756) ∨ (¬ p633) ∨ (¬ p533) ∨ p789 ∨ (¬ p1325) ∨ p790 ∨ (¬ p88) ∨ (¬ p577)) : (¬ p756) ∨ (¬ p633) ∨ p789 ∨ (¬ p1325) ∨ p790 ∨ (¬ p88) ∨ (¬ p577) := by
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
  have u2 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p533 := by
    exact h35501
  rcases h30381 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u7)
  · exact False.elim (u2 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (u4 q5)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step36340 (p14 p15 p124 p225 p664 p1076 : Prop)
    (h35502 : p664)
    (h30410 : p124 ∨ (¬ p1076) ∨ (¬ p15) ∨ p225 ∨ (¬ p664) ∨ (¬ p14)) : p124 ∨ (¬ p15) ∨ (¬ p1076) ∨ p225 ∨ (¬ p14) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p664 := by
    exact h35502
  rcases h30410 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u4)

theorem step36341 (p125 p303 p533 p1096 p1325 p1562 : Prop)
    (h35501 : p533)
    (h26020 : (¬ p1562) ∨ (¬ p1325) ∨ (¬ p1096) ∨ (¬ p303) ∨ (¬ p125) ∨ (¬ p533)) : (¬ p1562) ∨ (¬ p1096) ∨ (¬ p303) ∨ (¬ p1325) ∨ (¬ p125) := by
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
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p533 := by
    exact h35501
  rcases h26020 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)

theorem step36342 (p11 p15 p126 p234 p327 p961 : Prop)
    (h35549 : p327)
    (h30413 : p126 ∨ (¬ p961) ∨ (¬ p234) ∨ (¬ p327) ∨ (¬ p15) ∨ p11) : (¬ p234) ∨ p126 ∨ (¬ p961) ∨ (¬ p15) ∨ p11 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p327 := by
    exact h35549
  rcases h30413 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (u4 q5)

theorem step36344 (p124 p595 p726 p985 p1286 p1325 : Prop)
    (h35503 : p985)
    (h30421 : (¬ p1286) ∨ p1325 ∨ p124 ∨ (¬ p985) ∨ (¬ p726) ∨ (¬ p595)) : (¬ p1286) ∨ p124 ∨ p1325 ∨ (¬ p726) ∨ (¬ p595) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p985 := by
    exact h35503
  rcases h30421 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step36345 (p101 p121 p224 p227 p496 p897 p1096 : Prop)
    (h35500 : p496)
    (h30426 : p121 ∨ (¬ p897) ∨ p1096 ∨ (¬ p224) ∨ (¬ p496) ∨ p101 ∨ (¬ p227)) : (¬ p224) ∨ p1096 ∨ p121 ∨ (¬ p897) ∨ p101 ∨ (¬ p227) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p121) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p496 := by
    exact h35500
  rcases h30426 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u6)
  · exact False.elim (u4 q5)
  · exact False.elim (q6 u5)

theorem step36347 (p368 p496 p617 : Prop)
    (h35500 : p496)
    (h12436 : (¬ p368) ∨ (¬ p496) ∨ p617) : p617 ∨ (¬ p368) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p617) := fun hu => hn (Or.inl hu)
  have u1 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p496 := by
    exact h35500
  rcases h12436 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (u0 q2)

theorem step36348 (p10 p121 p125 p496 p1074 p1081 p1096 : Prop)
    (h35500 : p496)
    (h30428 : (¬ p10) ∨ p125 ∨ (¬ p1081) ∨ p1096 ∨ (¬ p121) ∨ (¬ p1074) ∨ (¬ p496)) : (¬ p10) ∨ p125 ∨ (¬ p1081) ∨ p1096 ∨ (¬ p121) ∨ (¬ p1074) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p125) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p496 := by
    exact h35500
  rcases h30428 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)

theorem step36349 (p41 p63 p124 p134 p224 p344 p496 : Prop)
    (h35500 : p496)
    (h30429 : p41 ∨ (¬ p124) ∨ (¬ p496) ∨ p63 ∨ (¬ p344) ∨ p224 ∨ (¬ p134)) : p41 ∨ p63 ∨ (¬ p124) ∨ (¬ p344) ∨ p224 ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p41) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p63) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p496 := by
    exact h35500
  rcases h30429 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (u4 q5)
  · exact False.elim (q6 u5)

theorem step36350 (p8 p15 p310 p344 p423 p496 p1044 p1076 : Prop)
    (h35500 : p496)
    (h30430 : p423 ∨ p1076 ∨ (¬ p496) ∨ p15 ∨ (¬ p310) ∨ p344 ∨ (¬ p8) ∨ (¬ p1044)) : p423 ∨ p15 ∨ p1076 ∨ (¬ p310) ∨ p344 ∨ (¬ p8) ∨ (¬ p1044) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1044 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p496 := by
    exact h35500
  rcases h30430 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (u4 q5)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step36351 (p14 p15 p227 p496 p940 p985 p1452 : Prop)
    (h35500 : p496)
    (h35503 : p985)
    (h30431 : p14 ∨ (¬ p940) ∨ (¬ p1452) ∨ (¬ p496) ∨ (¬ p227) ∨ (¬ p985) ∨ p15) : (¬ p1452) ∨ p14 ∨ (¬ p940) ∨ (¬ p227) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p14) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p496 := by
    exact h35500
  have u6 : p985 := by
    exact h35503
  rcases h30431 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (u4 q6)

theorem step36352 (p11 p126 p227 p347 p496 p897 p1096 : Prop)
    (h35500 : p496)
    (h35646 : p347)
    (h30432 : (¬ p227) ∨ (¬ p11) ∨ (¬ p496) ∨ p1096 ∨ (¬ p126) ∨ (¬ p347) ∨ (¬ p897)) : (¬ p227) ∨ (¬ p11) ∨ p1096 ∨ (¬ p126) ∨ (¬ p897) := by
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
  have u2 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p496 := by
    exact h35500
  have u6 : p347 := by
    exact h35646
  rcases h30432 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (u2 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u4)

theorem step36355 (p15 p124 p423 p496 p533 p756 p1465 : Prop)
    (h35501 : p533)
    (h35500 : p496)
    (h30435 : (¬ p756) ∨ p423 ∨ p15 ∨ (¬ p1465) ∨ (¬ p533) ∨ (¬ p124) ∨ (¬ p496)) : p423 ∨ (¬ p756) ∨ p15 ∨ (¬ p1465) ∨ (¬ p124) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p533 := by
    exact h35501
  have u6 : p496 := by
    exact h35500
  rcases h30435 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u6)

theorem step36356 (p2 p195 p419 p789 p797 : Prop)
    (h35556 : p195)
    (h30464 : (¬ p797) ∨ p419 ∨ p789 ∨ (¬ p195) ∨ p2) : (¬ p797) ∨ p789 ∨ p419 ∨ p2 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p797 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p789) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p195 := by
    exact h35556
  rcases h30464 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (u3 q4)

theorem step36357 (p2 p195 p797 p1015 p1366 : Prop)
    (h35556 : p195)
    (h30468 : (¬ p1366) ∨ (¬ p797) ∨ (¬ p195) ∨ p2 ∨ (¬ p1015)) : (¬ p1015) ∨ (¬ p797) ∨ p2 ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p797 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p195 := by
    exact h35556
  rcases h30468 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (u2 q3)
  · exact False.elim (q4 u0)

theorem step36358 (p2 p39 p63 p68 p864 p1002 p1035 p1229 p1269 p1325 : Prop)
    (h35495 : p39)
    (h30481 : (¬ p864) ∨ p1229 ∨ (¬ p1325) ∨ (¬ p63) ∨ (¬ p1035) ∨ p2 ∨ (¬ p39) ∨ (¬ p1002) ∨ (¬ p68) ∨ (¬ p1269)) : (¬ p864) ∨ p1229 ∨ (¬ p1325) ∨ (¬ p63) ∨ (¬ p1035) ∨ p2 ∨ (¬ p1002) ∨ (¬ p68) ∨ (¬ p1269) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p864 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1002 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1269 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p39 := by
    exact h35495
  rcases h30481 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step36359 (p2 p39 p63 p68 p419 p897 p1096 p1325 : Prop)
    (h35495 : p39)
    (h30482 : p1325 ∨ p1096 ∨ (¬ p68) ∨ p419 ∨ p2 ∨ (¬ p39) ∨ (¬ p897) ∨ (¬ p63)) : p2 ∨ p1096 ∨ (¬ p68) ∨ p419 ∨ p1325 ∨ (¬ p897) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p2) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p39 := by
    exact h35495
  rcases h30482 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u4 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (u0 q4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step36360 (p2 p12 p63 p539 p668 p836 p918 : Prop)
    (h35527 : p668)
    (h30489 : (¬ p12) ∨ (¬ p836) ∨ (¬ p539) ∨ p63 ∨ (¬ p668) ∨ (¬ p918) ∨ p2) : (¬ p918) ∨ (¬ p836) ∨ (¬ p539) ∨ p63 ∨ (¬ p12) ∨ p2 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p539 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p668 := by
    exact h35527
  rcases h30489 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u0)
  · exact False.elim (u5 q6)

theorem step36361 (p2 p39 p63 p68 p224 p419 p595 p906 : Prop)
    (h35495 : p39)
    (h30499 : (¬ p906) ∨ p419 ∨ (¬ p224) ∨ (¬ p68) ∨ p2 ∨ (¬ p63) ∨ p595 ∨ (¬ p39)) : (¬ p906) ∨ (¬ p224) ∨ p419 ∨ (¬ p68) ∨ p2 ∨ (¬ p63) ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p906 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p39 := by
    exact h35495
  rcases h30499 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)
  · exact False.elim (q7 u7)

theorem step36365 (p2 p41 p87 p187 p224 p542 p789 p790 : Prop)
    (h35497 : p87)
    (h30511 : (¬ p41) ∨ (¬ p542) ∨ p2 ∨ p224 ∨ (¬ p87) ∨ (¬ p187) ∨ p790 ∨ p789) : p789 ∨ (¬ p542) ∨ p2 ∨ p224 ∨ (¬ p187) ∨ p790 ∨ (¬ p41) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p789) := fun hu => hn (Or.inl hu)
  have u1 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p87 := by
    exact h35497
  rcases h30511 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u1)
  · exact False.elim (u2 q2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)
  · exact False.elim (u0 q7)

theorem step36367 (p2 p41 p195 p798 p1385 : Prop)
    (h35556 : p195)
    (h30518 : (¬ p798) ∨ (¬ p1385) ∨ (¬ p41) ∨ (¬ p195) ∨ p2) : (¬ p798) ∨ (¬ p1385) ∨ (¬ p41) ∨ p2 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p798 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p195 := by
    exact h35556
  rcases h30518 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (u3 q4)

theorem step36368 (p2 p185 p190 p303 p347 p419 p836 : Prop)
    (h35646 : p347)
    (h30520 : p419 ∨ (¬ p836) ∨ (¬ p347) ∨ (¬ p190) ∨ p2 ∨ (¬ p303) ∨ (¬ p185)) : (¬ p836) ∨ (¬ p190) ∨ p419 ∨ p2 ∨ (¬ p303) ∨ (¬ p185) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p347 := by
    exact h35646
  rcases h30520 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (u3 q4)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step36369 (p2 p16 p71 p185 p419 p985 p1325 p1584 : Prop)
    (h35503 : p985)
    (h35539 : p16)
    (h30522 : (¬ p1584) ∨ p419 ∨ p2 ∨ (¬ p985) ∨ (¬ p71) ∨ (¬ p16) ∨ p1325 ∨ (¬ p185)) : (¬ p1584) ∨ p2 ∨ p419 ∨ (¬ p71) ∨ p1325 ∨ (¬ p185) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p2) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p985 := by
    exact h35503
  have u7 : p16 := by
    exact h35539
  rcases h30522 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u7)
  · exact False.elim (u4 q6)
  · exact False.elim (q7 u5)

theorem step36370 (p2 p41 p87 p185 p187 p419 p926 p1074 : Prop)
    (h35497 : p87)
    (h30523 : (¬ p1074) ∨ p419 ∨ (¬ p185) ∨ (¬ p87) ∨ p2 ∨ (¬ p926) ∨ (¬ p41) ∨ (¬ p187)) : (¬ p1074) ∨ (¬ p185) ∨ p419 ∨ p2 ∨ (¬ p926) ∨ (¬ p41) ∨ (¬ p187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p926 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p87 := by
    exact h35497
  rcases h30523 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u7)
  · exact False.elim (u3 q4)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step36371 (p2 p41 p87 p185 p187 p419 p836 p897 : Prop)
    (h35497 : p87)
    (h30524 : (¬ p836) ∨ p897 ∨ (¬ p187) ∨ (¬ p41) ∨ p2 ∨ (¬ p87) ∨ p419 ∨ (¬ p185)) : p897 ∨ (¬ p836) ∨ (¬ p187) ∨ (¬ p41) ∨ p2 ∨ p419 ∨ (¬ p185) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p897) := fun hu => hn (Or.inl hu)
  have u1 : p836 := by
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
  have u4 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p87 := by
    exact h35497
  rcases h30524 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u7)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u6)

theorem step36372 (p2 p101 p124 p206 p330 : Prop)
    (h35499 : p330)
    (h30527 : p124 ∨ p101 ∨ (¬ p206) ∨ p2 ∨ (¬ p330)) : p2 ∨ p124 ∨ p101 ∨ (¬ p206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p2) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p330 := by
    exact h35499
  rcases h30527 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)

theorem step36373 (p2 p3 p12 p328 p348 p664 : Prop)
    (h35502 : p664)
    (h30528 : p3 ∨ (¬ p348) ∨ (¬ p328) ∨ (¬ p664) ∨ p2 ∨ p12) : (¬ p328) ∨ (¬ p348) ∨ p3 ∨ p2 ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p328 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p664 := by
    exact h35502
  rcases h30528 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (u3 q4)
  · exact False.elim (u4 q5)

theorem step36374 (p2 p18 p134 p195 p234 : Prop)
    (h35556 : p195)
    (h30532 : p234 ∨ p18 ∨ (¬ p195) ∨ p2 ∨ (¬ p134)) : p234 ∨ p2 ∨ p18 ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p2) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p195 := by
    exact h35556
  rcases h30532 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u3)

theorem step36375 (p2 p108 p330 p557 p836 p998 p1055 p1115 p1140 p1325 : Prop)
    (h35499 : p330)
    (h30534 : (¬ p1115) ∨ (¬ p998) ∨ (¬ p108) ∨ (¬ p1325) ∨ p1140 ∨ p2 ∨ (¬ p330) ∨ p836 ∨ p1055 ∨ (¬ p557)) : (¬ p998) ∨ (¬ p1115) ∨ (¬ p108) ∨ (¬ p1325) ∨ p1140 ∨ p2 ∨ p836 ∨ p1055 ∨ (¬ p557) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p998 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p330 := by
    exact h35499
  rcases h30534 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u9)
  · exact False.elim (u6 q7)
  · exact False.elim (u7 q8)
  · exact False.elim (q9 u8)

theorem step36376 (p2 p16 p71 p185 p234 p423 p1040 p1115 : Prop)
    (h35539 : p16)
    (h30537 : (¬ p1115) ∨ p234 ∨ p2 ∨ (¬ p185) ∨ (¬ p71) ∨ (¬ p16) ∨ (¬ p423) ∨ (¬ p1040)) : (¬ p1115) ∨ p234 ∨ p2 ∨ (¬ p185) ∨ (¬ p71) ∨ (¬ p423) ∨ (¬ p1040) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p234) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p71 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p16 := by
    exact h35539
  rcases h30537 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step36377 (p2 p41 p87 p161 p187 p1272 p1330 p1349 p1366 : Prop)
    (h35497 : p87)
    (h30541 : (¬ p1366) ∨ (¬ p41) ∨ (¬ p1330) ∨ (¬ p161) ∨ (¬ p187) ∨ (¬ p87) ∨ p2 ∨ (¬ p1349) ∨ (¬ p1272)) : p2 ∨ (¬ p1366) ∨ (¬ p1330) ∨ (¬ p161) ∨ (¬ p187) ∨ (¬ p41) ∨ (¬ p1349) ∨ (¬ p1272) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p2) := fun hu => hn (Or.inl hu)
  have u1 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p161 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1272 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p87 := by
    exact h35497
  rcases h30541 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u8)
  · exact False.elim (u0 q6)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step36378 (p3 p191 p382 p424 p476 p940 p985 p1325 : Prop)
    (h35503 : p985)
    (h30553 : (¬ p940) ∨ p382 ∨ (¬ p985) ∨ p1325 ∨ (¬ p191) ∨ (¬ p424) ∨ p3 ∨ (¬ p476)) : (¬ p940) ∨ p382 ∨ p1325 ∨ (¬ p191) ∨ (¬ p424) ∨ p3 ∨ (¬ p476) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p476 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p985 := by
    exact h35503
  rcases h30553 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (u2 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u6)

theorem step36380 (p195 p382 p419 p424 p475 : Prop)
    (h35556 : p195)
    (h30561 : p424 ∨ p382 ∨ (¬ p419) ∨ (¬ p195) ∨ (¬ p475)) : p424 ∨ (¬ p419) ∨ p382 ∨ (¬ p475) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p475 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p195 := by
    exact h35556
  rcases h30561 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)

theorem step36381 (p6 p330 p382 p419 p475 : Prop)
    (h35499 : p330)
    (h30563 : p382 ∨ (¬ p419) ∨ (¬ p330) ∨ (¬ p475) ∨ (¬ p6)) : (¬ p419) ∨ (¬ p475) ∨ p382 ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p475 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p330 := by
    exact h35499
  rcases h30563 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)

theorem step36382 (p84 p186 p344 p382 p475 p582 p634 p756 p789 p801 p1366 p1538 : Prop)
    (h35574 : p582)
    (h30566 : (¬ p634) ∨ p382 ∨ (¬ p186) ∨ (¬ p1366) ∨ (¬ p1538) ∨ (¬ p756) ∨ (¬ p84) ∨ p344 ∨ (¬ p801) ∨ (¬ p475) ∨ (¬ p582) ∨ p789) : p382 ∨ (¬ p634) ∨ (¬ p186) ∨ (¬ p1366) ∨ (¬ p1538) ∨ (¬ p756) ∨ (¬ p84) ∨ p344 ∨ (¬ p801) ∨ (¬ p475) ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p634 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1538 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p801 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p475 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : p582 := by
    exact h35574
  rcases h30566 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)
  · exact False.elim (u7 q7)
  · exact False.elim (q8 u8)
  · exact False.elim (q9 u9)
  · exact False.elim (q10 u11)
  · exact False.elim (u10 q11)

theorem step36383 (p10 p39 p63 p68 p121 p125 p211 p464 p1229 : Prop)
    (h35495 : p39)
    (h30570 : (¬ p464) ∨ p1229 ∨ (¬ p211) ∨ (¬ p10) ∨ (¬ p121) ∨ (¬ p68) ∨ (¬ p63) ∨ (¬ p39) ∨ p125) : (¬ p464) ∨ p1229 ∨ (¬ p211) ∨ (¬ p10) ∨ (¬ p121) ∨ (¬ p68) ∨ (¬ p63) ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p464 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p39 := by
    exact h35495
  rcases h30570 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u8)
  · exact False.elim (u7 q8)

theorem step36384 (p13 p86 p161 p185 p457 p495 p1115 p1452 : Prop)
    (h35496 : p86)
    (h30599 : (¬ p457) ∨ (¬ p13) ∨ (¬ p161) ∨ p185 ∨ (¬ p1452) ∨ p1115 ∨ (¬ p86) ∨ (¬ p495)) : (¬ p457) ∨ (¬ p495) ∨ (¬ p161) ∨ p185 ∨ (¬ p1452) ∨ p1115 ∨ (¬ p13) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p457 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p86 := by
    exact h35496
  rcases h30599 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u1)

theorem step36386 (p41 p137 p330 p424 p576 : Prop)
    (h35499 : p330)
    (h16302 : (¬ p41) ∨ (¬ p137) ∨ (¬ p330) ∨ (¬ p424) ∨ (¬ p576)) : (¬ p576) ∨ (¬ p424) ∨ (¬ p137) ∨ (¬ p41) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p137 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p330 := by
    exact h35499
  rcases h16302 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)

theorem step36387 (p41 p63 p224 p382 p424 p542 p709 p1103 : Prop)
    (h35504 : p1103)
    (h30608 : (¬ p41) ∨ (¬ p709) ∨ p224 ∨ (¬ p1103) ∨ (¬ p382) ∨ (¬ p424) ∨ (¬ p63) ∨ (¬ p542)) : (¬ p63) ∨ (¬ p709) ∨ p224 ∨ (¬ p382) ∨ (¬ p424) ∨ (¬ p41) ∨ (¬ p542) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p709 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1103 := by
    exact h35504
  rcases h30608 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u6)

theorem step36388 (p86 p189 p419 p424 p431 p595 p1545 : Prop)
    (h35496 : p86)
    (h30609 : (¬ p431) ∨ p419 ∨ (¬ p1545) ∨ p189 ∨ p595 ∨ (¬ p86) ∨ (¬ p424)) : (¬ p1545) ∨ p189 ∨ (¬ p431) ∨ p419 ∨ p595 ∨ (¬ p424) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p86 := by
    exact h35496
  rcases h30609 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (u1 q3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u5)

theorem step36389 (p86 p189 p224 p424 p542 p595 p1287 : Prop)
    (h35496 : p86)
    (h30610 : (¬ p542) ∨ p189 ∨ (¬ p1287) ∨ p595 ∨ (¬ p424) ∨ p224 ∨ (¬ p86)) : (¬ p1287) ∨ p189 ∨ (¬ p542) ∨ p595 ∨ (¬ p424) ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p86 := by
    exact h35496
  rcases h30610 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)

theorem step36390 (p86 p189 p419 p424 p1074 p1096 : Prop)
    (h35496 : p86)
    (h30611 : (¬ p1074) ∨ p419 ∨ p189 ∨ (¬ p86) ∨ p1096 ∨ (¬ p424)) : (¬ p1074) ∨ p189 ∨ p419 ∨ p1096 ∨ (¬ p424) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p86 := by
    exact h35496
  rcases h30611 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u5)
  · exact False.elim (u3 q4)
  · exact False.elim (q5 u4)

theorem step36391 (p84 p189 p419 p424 p495 p582 p1229 p1295 : Prop)
    (h35574 : p582)
    (h30618 : (¬ p1295) ∨ p419 ∨ (¬ p424) ∨ p495 ∨ (¬ p582) ∨ p1229 ∨ (¬ p84) ∨ p189) : (¬ p1295) ∨ (¬ p424) ∨ p419 ∨ p495 ∨ p1229 ∨ (¬ p84) ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1295 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p582 := by
    exact h35574
  rcases h30618 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u7)
  · exact False.elim (u4 q5)
  · exact False.elim (q6 u5)
  · exact False.elim (u6 q7)

theorem step36392 (p2 p41 p87 p188 p424 : Prop)
    (h35497 : p87)
    (h17092 : (¬ p2) ∨ (¬ p41) ∨ (¬ p87) ∨ (¬ p188) ∨ (¬ p424)) : (¬ p2) ∨ (¬ p188) ∨ (¬ p41) ∨ (¬ p424) := by
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
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p87 := by
    exact h35497
  rcases h17092 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)

theorem step36394 (p86 p189 p344 p424 p495 p542 p633 : Prop)
    (h35496 : p86)
    (h30626 : p633 ∨ p189 ∨ (¬ p86) ∨ (¬ p424) ∨ (¬ p542) ∨ (¬ p495) ∨ p344) : (¬ p424) ∨ p633 ∨ p189 ∨ (¬ p542) ∨ (¬ p495) ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p633) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p86 := by
    exact h35496
  rcases h30626 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)

theorem step36396 (p84 p189 p344 p424 p495 p542 p582 p635 p1096 : Prop)
    (h35574 : p582)
    (h30630 : (¬ p635) ∨ p1096 ∨ (¬ p84) ∨ (¬ p424) ∨ (¬ p582) ∨ p344 ∨ p495 ∨ (¬ p542) ∨ p189) : (¬ p424) ∨ p1096 ∨ (¬ p84) ∨ (¬ p635) ∨ p344 ∨ p495 ∨ (¬ p542) ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p635 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p582 := by
    exact h35574
  rcases h30630 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u3)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u8)
  · exact False.elim (u4 q5)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u6)
  · exact False.elim (u7 q8)

theorem step36397 (p17 p137 p189 p330 p424 : Prop)
    (h35499 : p330)
    (h30632 : p189 ∨ (¬ p17) ∨ (¬ p137) ∨ (¬ p424) ∨ (¬ p330)) : (¬ p17) ∨ (¬ p137) ∨ p189 ∨ (¬ p424) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p137 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p330 := by
    exact h35499
  rcases h30632 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)

theorem step36398 (p2 p163 p188 p263 p310 p344 p424 p1055 p1076 : Prop)
    (h35554 : p263)
    (h30636 : (¬ p2) ∨ p163 ∨ (¬ p263) ∨ (¬ p424) ∨ (¬ p344) ∨ (¬ p310) ∨ (¬ p1076) ∨ (¬ p188) ∨ p1055) : (¬ p344) ∨ (¬ p424) ∨ (¬ p2) ∨ p163 ∨ (¬ p310) ∨ (¬ p1076) ∨ (¬ p188) ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p263 := by
    exact h35554
  rcases h30636 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (u7 q8)

theorem step36399 (p84 p124 p189 p419 p424 p425 p582 p1076 : Prop)
    (h35574 : p582)
    (h30638 : (¬ p425) ∨ p124 ∨ p189 ∨ (¬ p84) ∨ (¬ p424) ∨ (¬ p1076) ∨ p419 ∨ (¬ p582)) : p124 ∨ p189 ∨ (¬ p425) ∨ (¬ p84) ∨ (¬ p424) ∨ (¬ p1076) ∨ p419 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p582 := by
    exact h35574
  rcases h30638 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)
  · exact False.elim (q7 u7)

theorem step36400 (p224 p404 p897 p1096 p1233 : Prop)
    (h35505 : p1233)
    (h30684 : (¬ p404) ∨ p1096 ∨ (¬ p897) ∨ (¬ p224) ∨ (¬ p1233)) : (¬ p404) ∨ p1096 ∨ (¬ p897) ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p404 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1233 := by
    exact h35505
  rcases h30684 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)

theorem step36403 (p18 p47 p87 p121 p189 p382 p389 p816 p1385 : Prop)
    (h35497 : p87)
    (h30692 : (¬ p389) ∨ (¬ p47) ∨ p121 ∨ p382 ∨ p1385 ∨ (¬ p87) ∨ (¬ p816) ∨ (¬ p189) ∨ (¬ p18)) : (¬ p389) ∨ p121 ∨ (¬ p47) ∨ p382 ∨ p1385 ∨ (¬ p816) ∨ (¬ p189) ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p121) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p816 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p87 := by
    exact h35497
  rcases h30692 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u3 q3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step36404 (p86 p389 p455 p495 p1325 p1346 p1508 : Prop)
    (h35496 : p86)
    (h30695 : p455 ∨ (¬ p1346) ∨ (¬ p86) ∨ (¬ p389) ∨ (¬ p1508) ∨ (¬ p1325) ∨ (¬ p495)) : p455 ∨ (¬ p389) ∨ (¬ p1346) ∨ (¬ p1508) ∨ (¬ p1325) ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : p389 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p86 := by
    exact h35496
  rcases h30695 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step36405 (p86 p185 p224 p389 p455 p495 p836 : Prop)
    (h35496 : p86)
    (h30697 : p455 ∨ p224 ∨ (¬ p86) ∨ p836 ∨ (¬ p495) ∨ (¬ p389) ∨ p185) : p455 ∨ p836 ∨ p224 ∨ (¬ p495) ∨ (¬ p389) ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p836) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p86 := by
    exact h35496
  rcases h30697 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)

theorem step36406 (p86 p189 p389 p419 p424 p455 p495 : Prop)
    (h35496 : p86)
    (h30700 : p455 ∨ (¬ p389) ∨ (¬ p495) ∨ p419 ∨ (¬ p424) ∨ p189 ∨ (¬ p86)) : p455 ∨ (¬ p389) ∨ (¬ p495) ∨ p419 ∨ (¬ p424) ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p86 := by
    exact h35496
  rcases h30700 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)

theorem step36408 (p44 p189 p234 p265 p303 p327 p363 p382 p576 : Prop)
    (h35549 : p327)
    (h30738 : (¬ p382) ∨ p303 ∨ (¬ p576) ∨ (¬ p234) ∨ p189 ∨ (¬ p327) ∨ (¬ p265) ∨ (¬ p44) ∨ (¬ p363)) : p303 ∨ (¬ p576) ∨ (¬ p382) ∨ (¬ p234) ∨ p189 ∨ (¬ p265) ∨ (¬ p44) ∨ (¬ p363) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p363 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p327 := by
    exact h35549
  rcases h30738 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step36409 (p134 p189 p330 p790 : Prop)
    (h35499 : p330)
    (h23538 : (¬ p790) ∨ (¬ p134) ∨ (¬ p330) ∨ (¬ p189)) : (¬ p790) ∨ (¬ p134) ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p790 := by
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
    exact hn (Or.inr (Or.inr hu))
  have u3 : p330 := by
    exact h35499
  rcases h23538 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)

theorem step36410 (p125 p327 p435 p441 p1631 : Prop)
    (h35549 : p327)
    (h17728 : (¬ p125) ∨ (¬ p327) ∨ (¬ p435) ∨ (¬ p441) ∨ (¬ p1631)) : (¬ p441) ∨ (¬ p1631) ∨ (¬ p125) ∨ (¬ p435) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p441 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1631 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p327 := by
    exact h35549
  rcases h17728 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)

theorem step36412 (p39 p63 p68 p327 p382 p419 p420 p475 p495 : Prop)
    (h35549 : p327)
    (h35495 : p39)
    (h30748 : p382 ∨ (¬ p68) ∨ (¬ p475) ∨ (¬ p419) ∨ (¬ p327) ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p63) ∨ (¬ p39)) : (¬ p475) ∨ p382 ∨ (¬ p68) ∨ (¬ p419) ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p475 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p327 := by
    exact h35549
  have u8 : p39 := by
    exact h35495
  rcases h30748 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u8)

theorem step36413 (p86 p327 p419 p420 p495 p789 p790 : Prop)
    (h35496 : p86)
    (h35549 : p327)
    (h16211 : (¬ p86) ∨ (¬ p327) ∨ (¬ p419) ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p789) ∨ (¬ p790)) : (¬ p790) ∨ (¬ p420) ∨ (¬ p789) ∨ (¬ p495) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p86 := by
    exact h35496
  have u6 : p327 := by
    exact h35549
  rcases h16211 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u0)

theorem step36414 (p125 p227 p327 p383 p419 : Prop)
    (h35549 : p327)
    (h16232 : (¬ p125) ∨ (¬ p227) ∨ (¬ p327) ∨ (¬ p383) ∨ (¬ p419)) : (¬ p383) ∨ (¬ p419) ∨ (¬ p227) ∨ (¬ p125) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p383 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p419 := by
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
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p327 := by
    exact h35549
  rcases h16232 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)

theorem step36415 (p124 p327 p382 p419 p420 p494 p617 p633 : Prop)
    (h35549 : p327)
    (h30749 : p382 ∨ (¬ p420) ∨ (¬ p419) ∨ (¬ p327) ∨ (¬ p633) ∨ p124 ∨ (¬ p494) ∨ (¬ p617)) : (¬ p419) ∨ p382 ∨ (¬ p420) ∨ (¬ p633) ∨ p124 ∨ (¬ p494) ∨ (¬ p617) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p617 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p327 := by
    exact h35549
  rcases h30749 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u3)
  · exact False.elim (u4 q5)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step36444 (p8 p12 p14 p44 p189 p241 p668 p918 : Prop)
    (h35527 : p668)
    (h30882 : (¬ p241) ∨ (¬ p918) ∨ (¬ p44) ∨ p8 ∨ (¬ p668) ∨ p189 ∨ (¬ p12) ∨ (¬ p14)) : (¬ p918) ∨ (¬ p241) ∨ (¬ p44) ∨ p8 ∨ p189 ∨ (¬ p12) ∨ (¬ p14) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p668 := by
    exact h35527
  rcases h30882 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u7)
  · exact False.elim (u4 q5)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step36446 (p195 p382 p424 p480 p665 p980 p1140 p1253 p1508 : Prop)
    (h35556 : p195)
    (h30956 : p424 ∨ (¬ p1253) ∨ (¬ p980) ∨ (¬ p1508) ∨ (¬ p382) ∨ (¬ p1140) ∨ (¬ p195) ∨ (¬ p480) ∨ (¬ p665)) : p424 ∨ (¬ p980) ∨ (¬ p1253) ∨ (¬ p1508) ∨ (¬ p382) ∨ (¬ p1140) ∨ (¬ p480) ∨ (¬ p665) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1253 := by
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
  have u6 : p480 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p195 := by
    exact h35556
  rcases h30956 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step36447 (p10 p17 p140 p171 p189 p224 p241 p347 p382 p709 : Prop)
    (h35646 : p347)
    (h30962 : (¬ p171) ∨ (¬ p241) ∨ (¬ p709) ∨ (¬ p382) ∨ (¬ p347) ∨ p10 ∨ p17 ∨ p224 ∨ (¬ p140) ∨ (¬ p189)) : (¬ p171) ∨ (¬ p382) ∨ (¬ p709) ∨ (¬ p241) ∨ p10 ∨ p17 ∨ p224 ∨ (¬ p140) ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p171 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p709 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p347 := by
    exact h35646
  rcases h30962 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u9)
  · exact False.elim (u4 q5)
  · exact False.elim (u5 q6)
  · exact False.elim (u6 q7)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step36448 (p15 p18 p170 p326 p424 p1055 p1103 p1115 : Prop)
    (h35504 : p1103)
    (h30978 : p424 ∨ (¬ p15) ∨ p18 ∨ (¬ p1103) ∨ (¬ p1055) ∨ (¬ p170) ∨ p1115 ∨ (¬ p326)) : p424 ∨ (¬ p170) ∨ (¬ p15) ∨ p18 ∨ (¬ p1055) ∨ p1115 ∨ (¬ p326) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p170 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p326 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1103 := by
    exact h35504
  rcases h30978 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (u3 q2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u1)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u6)

theorem step36451 (p41 p156 p157 p158 p159 p160 p161 : Prop)
    (h35659 : p156)
    (h16158 : (¬ p41) ∨ (¬ p156) ∨ (¬ p157) ∨ (¬ p158) ∨ (¬ p159) ∨ (¬ p160) ∨ (¬ p161)) : (¬ p160) ∨ (¬ p161) ∨ (¬ p41) ∨ (¬ p157) ∨ (¬ p159) ∨ (¬ p158) := by
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
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p157 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p156 := by
    exact h35659
  rcases h16158 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u1)

theorem step36452 (p8 p157 p160 p668 p980 : Prop)
    (h35527 : p668)
    (h31013 : (¬ p157) ∨ (¬ p160) ∨ (¬ p980) ∨ p8 ∨ (¬ p668)) : (¬ p160) ∨ (¬ p157) ∨ (¬ p980) ∨ p8 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p157 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p668 := by
    exact h35527
  rcases h31013 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)

theorem step36453 (p125 p126 p136 p156 p185 p266 : Prop)
    (h35659 : p156)
    (h31014 : p126 ∨ (¬ p156) ∨ p125 ∨ (¬ p185) ∨ (¬ p266) ∨ (¬ p136)) : p126 ∨ (¬ p185) ∨ p125 ∨ (¬ p266) ∨ (¬ p136) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p136 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p156 := by
    exact h35659
  rcases h31014 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step36454 (p124 p138 p189 p258 p261 : Prop)
    (h35668 : p138)
    (h31042 : (¬ p261) ∨ p124 ∨ (¬ p138) ∨ p258 ∨ p189) : p258 ∨ p124 ∨ (¬ p261) ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p258) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p138 := by
    exact h35668
  rcases h31042 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (u0 q3)
  · exact False.elim (u3 q4)

theorem step36455 (p138 p165 p576 p927 p1095 p1115 : Prop)
    (h35668 : p138)
    (h17364 : (¬ p138) ∨ (¬ p165) ∨ (¬ p576) ∨ (¬ p927) ∨ (¬ p1095) ∨ (¬ p1115)) : (¬ p165) ∨ (¬ p1115) ∨ (¬ p1095) ∨ (¬ p576) ∨ (¬ p927) := by
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
  have u2 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p927 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p138 := by
    exact h35668
  rcases h17364 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u1)

theorem step36456 (p17 p138 p185 p419 p545 p789 p797 p836 : Prop)
    (h35668 : p138)
    (h31043 : (¬ p797) ∨ (¬ p545) ∨ p419 ∨ p185 ∨ p836 ∨ p789 ∨ (¬ p138) ∨ (¬ p17)) : (¬ p797) ∨ p419 ∨ (¬ p545) ∨ p185 ∨ p836 ∨ p789 ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p797 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p419) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p138 := by
    exact h35668
  rcases h31043 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u3 q3)
  · exact False.elim (u4 q4)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u6)

theorem step36459 (p48 p138 p576 p1711 p1712 : Prop)
    (h35668 : p138)
    (h17596 : (¬ p48) ∨ (¬ p138) ∨ (¬ p576) ∨ (¬ p1711) ∨ (¬ p1712)) : (¬ p1711) ∨ (¬ p1712) ∨ (¬ p48) ∨ (¬ p576) := by
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
  have u3 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p138 := by
    exact h35668
  rcases h17596 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)

theorem step36461 (p125 p138 p185 p189 p262 p303 p836 p1325 : Prop)
    (h35668 : p138)
    (h31047 : (¬ p836) ∨ p303 ∨ (¬ p185) ∨ p189 ∨ p125 ∨ (¬ p138) ∨ p1325 ∨ (¬ p262)) : (¬ p836) ∨ p303 ∨ (¬ p185) ∨ p189 ∨ p125 ∨ p1325 ∨ (¬ p262) := by
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
  have u5 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p138 := by
    exact h35668
  rcases h31047 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u7)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u6)

theorem step36462 (p41 p138 p575 p1604 p1651 : Prop)
    (h35668 : p138)
    (h17946 : (¬ p41) ∨ (¬ p138) ∨ (¬ p575) ∨ (¬ p1604) ∨ (¬ p1651)) : (¬ p1651) ∨ (¬ p1604) ∨ (¬ p41) ∨ (¬ p575) := by
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
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p575 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p138 := by
    exact h35668
  rcases h17946 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)

theorem step36464 (p125 p138 p189 p262 p434 p789 p790 : Prop)
    (h35668 : p138)
    (h31049 : (¬ p434) ∨ p790 ∨ p189 ∨ p789 ∨ p125 ∨ (¬ p262) ∨ (¬ p138)) : p790 ∨ (¬ p434) ∨ p189 ∨ p789 ∨ p125 ∨ (¬ p262) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p790) := fun hu => hn (Or.inl hu)
  have u1 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p138 := by
    exact h35668
  rcases h31049 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)
  · exact False.elim (u2 q2)
  · exact False.elim (u3 q3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)

theorem step36465 (p11 p138 p189 p261 p961 : Prop)
    (h35668 : p138)
    (h31050 : (¬ p961) ∨ (¬ p261) ∨ (¬ p138) ∨ p11 ∨ p189) : (¬ p261) ∨ (¬ p961) ∨ p11 ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p138 := by
    exact h35668
  rcases h31050 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (u2 q3)
  · exact False.elim (u3 q4)

theorem step36466 (p126 p138 p189 p515 p790 : Prop)
    (h35668 : p138)
    (h31051 : (¬ p515) ∨ p790 ∨ p189 ∨ (¬ p138) ∨ (¬ p126)) : p790 ∨ (¬ p515) ∨ p189 ∨ (¬ p126) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p790) := fun hu => hn (Or.inl hu)
  have u1 : p515 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p138 := by
    exact h35668
  rcases h31051 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)

theorem step36467 (p3 p12 p17 p138 p192 p980 p1512 p1758 : Prop)
    (h35668 : p138)
    (h31052 : (¬ p1512) ∨ (¬ p1758) ∨ (¬ p17) ∨ (¬ p192) ∨ (¬ p980) ∨ (¬ p138) ∨ p3 ∨ p12) : (¬ p1512) ∨ (¬ p1758) ∨ (¬ p17) ∨ (¬ p192) ∨ (¬ p980) ∨ p3 ∨ p12 := by
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
  have u5 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p138 := by
    exact h35668
  rcases h31052 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u7)
  · exact False.elim (u5 q6)
  · exact False.elim (u6 q7)

theorem step36468 (p124 p138 p185 p189 p262 p668 p836 p1076 : Prop)
    (h35668 : p138)
    (h35527 : p668)
    (h31053 : (¬ p836) ∨ p1076 ∨ (¬ p138) ∨ (¬ p262) ∨ (¬ p185) ∨ p189 ∨ (¬ p124) ∨ (¬ p668)) : (¬ p836) ∨ (¬ p262) ∨ p1076 ∨ (¬ p185) ∨ p189 ∨ (¬ p124) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p138 := by
    exact h35668
  have u7 : p668 := by
    exact h35527
  rcases h31053 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)
  · exact False.elim (u4 q5)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u7)

theorem step36469 (p138 p166 p185 p189 p225 p262 p303 p347 p368 p382 : Prop)
    (h35646 : p347)
    (h35668 : p138)
    (h31054 : (¬ p185) ∨ p382 ∨ (¬ p347) ∨ (¬ p225) ∨ (¬ p303) ∨ (¬ p138) ∨ (¬ p262) ∨ (¬ p368) ∨ p189 ∨ (¬ p166)) : p382 ∨ (¬ p185) ∨ (¬ p225) ∨ (¬ p303) ∨ (¬ p262) ∨ (¬ p368) ∨ p189 ∨ (¬ p166) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p166 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p347 := by
    exact h35646
  have u9 : p138 := by
    exact h35668
  rcases h31054 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (u6 q8)
  · exact False.elim (q9 u7)

theorem step36471 (p41 p138 p262 p368 p382 p1287 p1387 : Prop)
    (h35668 : p138)
    (h31056 : p382 ∨ (¬ p41) ∨ (¬ p1287) ∨ (¬ p138) ∨ (¬ p262) ∨ (¬ p1387) ∨ (¬ p368)) : (¬ p1287) ∨ p382 ∨ (¬ p41) ∨ (¬ p262) ∨ (¬ p1387) ∨ (¬ p368) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p138 := by
    exact h35668
  rcases h31056 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step36473 (p8 p17 p138 p165 p242 p836 : Prop)
    (h35668 : p138)
    (h18887 : (¬ p8) ∨ (¬ p17) ∨ (¬ p138) ∨ (¬ p165) ∨ (¬ p242) ∨ (¬ p836)) : (¬ p165) ∨ (¬ p836) ∨ (¬ p242) ∨ (¬ p17) ∨ (¬ p8) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p165 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p138 := by
    exact h35668
  rcases h18887 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u1)

theorem step36474 (p3 p14 p48 p138 p192 p576 : Prop)
    (h35668 : p138)
    (h31057 : p3 ∨ (¬ p192) ∨ (¬ p138) ∨ (¬ p14) ∨ (¬ p576) ∨ (¬ p48)) : (¬ p14) ∨ (¬ p192) ∨ p3 ∨ (¬ p576) ∨ (¬ p48) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p138 := by
    exact h35668
  rcases h31057 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step36475 (p3 p14 p17 p138 p192 p234 p790 p800 : Prop)
    (h35668 : p138)
    (h31058 : (¬ p800) ∨ p3 ∨ (¬ p790) ∨ (¬ p192) ∨ (¬ p138) ∨ p234 ∨ (¬ p14) ∨ (¬ p17)) : (¬ p800) ∨ (¬ p790) ∨ p3 ∨ (¬ p192) ∨ p234 ∨ (¬ p14) ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p800 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p234) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p138 := by
    exact h35668
  rcases h31058 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u7)
  · exact False.elim (u4 q5)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step36476 (p41 p63 p138 p495 p574 : Prop)
    (h35668 : p138)
    (h17220 : (¬ p41) ∨ (¬ p63) ∨ (¬ p138) ∨ (¬ p495) ∨ (¬ p574)) : (¬ p63) ∨ (¬ p574) ∨ (¬ p41) ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p574 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p138 := by
    exact h35668
  rcases h17220 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)

theorem step36479 (p17 p47 p138 p382 p820 p879 p898 p1287 : Prop)
    (h35668 : p138)
    (h31061 : p382 ∨ (¬ p820) ∨ (¬ p47) ∨ (¬ p138) ∨ (¬ p879) ∨ (¬ p17) ∨ (¬ p1287) ∨ (¬ p898)) : (¬ p820) ∨ p382 ∨ (¬ p47) ∨ (¬ p879) ∨ (¬ p17) ∨ (¬ p1287) ∨ (¬ p898) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p820 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p879 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p898 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p138 := by
    exact h35668
  rcases h31061 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step36480 (p8 p17 p47 p138 p242 p879 p897 : Prop)
    (h35668 : p138)
    (h17214 : (¬ p8) ∨ (¬ p17) ∨ (¬ p47) ∨ (¬ p138) ∨ (¬ p242) ∨ (¬ p879) ∨ (¬ p897)) : (¬ p879) ∨ (¬ p242) ∨ (¬ p47) ∨ (¬ p17) ∨ (¬ p8) ∨ (¬ p897) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p879 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p138 := by
    exact h35668
  rcases h17214 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u5)

theorem step36481 (p125 p126 p138 p189 p261 : Prop)
    (h35668 : p138)
    (h31062 : (¬ p125) ∨ p189 ∨ (¬ p126) ∨ (¬ p138) ∨ (¬ p261)) : (¬ p126) ∨ (¬ p125) ∨ p189 ∨ (¬ p261) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p138 := by
    exact h35668
  rcases h31062 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)

theorem step36482 (p3 p17 p138 p163 p186 : Prop)
    (h35668 : p138)
    (h31063 : (¬ p3) ∨ p163 ∨ (¬ p186) ∨ (¬ p138) ∨ (¬ p17)) : p163 ∨ (¬ p3) ∨ (¬ p186) ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p163) := fun hu => hn (Or.inl hu)
  have u1 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p138 := by
    exact h35668
  rcases h31063 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)

theorem step36483 (p17 p41 p138 p1249 p1346 : Prop)
    (h35668 : p138)
    (h17920 : (¬ p17) ∨ (¬ p41) ∨ (¬ p138) ∨ (¬ p1249) ∨ (¬ p1346)) : (¬ p1249) ∨ (¬ p1346) ∨ (¬ p41) ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p138 := by
    exact h35668
  rcases h17920 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)

theorem step36484 (p17 p41 p138 p790 p1385 : Prop)
    (h35668 : p138)
    (h18307 : (¬ p17) ∨ (¬ p41) ∨ (¬ p138) ∨ (¬ p790) ∨ (¬ p1385)) : (¬ p1385) ∨ (¬ p790) ∨ (¬ p41) ∨ (¬ p17) := by
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
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p138 := by
    exact h35668
  rcases h18307 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)

theorem step36485 (p15 p16 p106 p185 p344 p423 p836 p1037 : Prop)
    (h35539 : p16)
    (h20497 : (¬ p15) ∨ (¬ p16) ∨ (¬ p106) ∨ (¬ p185) ∨ (¬ p344) ∨ (¬ p423) ∨ (¬ p836) ∨ (¬ p1037)) : (¬ p1037) ∨ (¬ p836) ∨ (¬ p344) ∨ (¬ p185) ∨ (¬ p106) ∨ (¬ p423) ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1037 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p16 := by
    exact h35539
  rcases h20497 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u0)

theorem step36486 (p88 p185 p434 p576 p668 p690 p709 p836 p1055 : Prop)
    (h35527 : p668)
    (h31091 : (¬ p690) ∨ (¬ p434) ∨ (¬ p709) ∨ (¬ p836) ∨ (¬ p185) ∨ (¬ p88) ∨ p576 ∨ (¬ p668) ∨ p1055) : (¬ p690) ∨ (¬ p434) ∨ (¬ p709) ∨ (¬ p836) ∨ (¬ p185) ∨ (¬ p88) ∨ p576 ∨ p1055 := by
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
  have u7 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p668 := by
    exact h35527
  rcases h31091 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)
  · exact False.elim (q7 u8)
  · exact False.elim (u7 q8)

theorem step36488 (p39 p68 p88 p185 p211 p368 p382 p419 p739 p1366 p1584 : Prop)
    (h35495 : p39)
    (h31093 : (¬ p739) ∨ (¬ p1366) ∨ p382 ∨ (¬ p368) ∨ (¬ p419) ∨ (¬ p39) ∨ (¬ p1584) ∨ (¬ p68) ∨ (¬ p185) ∨ (¬ p211) ∨ (¬ p88)) : (¬ p739) ∨ (¬ p1366) ∨ p382 ∨ (¬ p368) ∨ (¬ p419) ∨ (¬ p1584) ∨ (¬ p68) ∨ (¬ p185) ∨ (¬ p211) ∨ (¬ p88) := by
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
  have u5 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p39 := by
    exact h35495
  rcases h31093 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)
  · exact False.elim (q10 u9)

theorem step36489 (p15 p39 p88 p690 p789 p815 p1022 p1229 p1291 : Prop)
    (h35495 : p39)
    (h31094 : (¬ p1229) ∨ p15 ∨ (¬ p690) ∨ p789 ∨ (¬ p1022) ∨ (¬ p88) ∨ (¬ p1291) ∨ (¬ p39) ∨ (¬ p815)) : (¬ p1229) ∨ (¬ p690) ∨ p15 ∨ p789 ∨ (¬ p1022) ∨ (¬ p88) ∨ (¬ p1291) ∨ (¬ p815) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
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
  have u7 : p815 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p39 := by
    exact h35495
  rcases h31094 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u7)

theorem step36490 (p15 p39 p88 p185 p224 p836 p1229 p1291 : Prop)
    (h35495 : p39)
    (h31095 : (¬ p836) ∨ (¬ p224) ∨ (¬ p1291) ∨ p15 ∨ (¬ p1229) ∨ (¬ p39) ∨ (¬ p185) ∨ (¬ p88)) : (¬ p836) ∨ (¬ p1229) ∨ (¬ p1291) ∨ p15 ∨ (¬ p224) ∨ (¬ p185) ∨ (¬ p88) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1291 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p39 := by
    exact h35495
  rcases h31095 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step36491 (p15 p39 p88 p185 p347 p420 p495 p836 : Prop)
    (h35495 : p39)
    (h35646 : p347)
    (h31096 : (¬ p836) ∨ p495 ∨ (¬ p185) ∨ (¬ p88) ∨ p15 ∨ (¬ p39) ∨ p420 ∨ (¬ p347)) : (¬ p836) ∨ (¬ p185) ∨ p495 ∨ (¬ p88) ∨ p15 ∨ p420 := by
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
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p39 := by
    exact h35495
  have u7 : p347 := by
    exact h35646
  rcases h31096 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u6)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u7)

theorem step36492 (p15 p39 p88 p106 p185 p344 p836 p883 p1096 : Prop)
    (h35495 : p39)
    (h31097 : (¬ p1096) ∨ (¬ p836) ∨ (¬ p39) ∨ (¬ p883) ∨ (¬ p344) ∨ (¬ p88) ∨ (¬ p106) ∨ p15 ∨ (¬ p185)) : (¬ p836) ∨ (¬ p1096) ∨ (¬ p883) ∨ (¬ p344) ∨ (¬ p88) ∨ (¬ p106) ∨ p15 ∨ (¬ p185) := by
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
  have u2 : p883 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p39 := by
    exact h35495
  rcases h31097 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (u6 q7)
  · exact False.elim (q8 u7)

theorem step36493 (p15 p39 p88 p185 p668 p836 p1095 p1096 : Prop)
    (h35495 : p39)
    (h35527 : p668)
    (h31098 : (¬ p1096) ∨ p15 ∨ (¬ p88) ∨ (¬ p836) ∨ (¬ p1095) ∨ (¬ p39) ∨ (¬ p668) ∨ (¬ p185)) : (¬ p88) ∨ (¬ p1096) ∨ p15 ∨ (¬ p836) ∨ (¬ p1095) ∨ (¬ p185) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p39 := by
    exact h35495
  have u7 : p668 := by
    exact h35527
  rcases h31098 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u5)

theorem step36494 (p39 p88 p124 p161 p224 p261 p344 p1000 p1146 p1465 : Prop)
    (h35495 : p39)
    (h31099 : p124 ∨ p161 ∨ (¬ p224) ∨ (¬ p261) ∨ (¬ p1000) ∨ (¬ p1146) ∨ (¬ p88) ∨ (¬ p1465) ∨ (¬ p39) ∨ p344) : p161 ∨ (¬ p224) ∨ p124 ∨ (¬ p261) ∨ (¬ p1000) ∨ (¬ p1146) ∨ (¬ p88) ∨ (¬ p1465) ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p161) := fun hu => hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
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
  have u8 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p39 := by
    exact h35495
  rcases h31099 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u9)
  · exact False.elim (u8 q9)

theorem step36495 (p6 p39 p88 p124 p224 p261 p344 p423 p1140 : Prop)
    (h35495 : p39)
    (h31100 : p1140 ∨ p124 ∨ (¬ p224) ∨ p344 ∨ (¬ p88) ∨ p6 ∨ (¬ p261) ∨ (¬ p39) ∨ (¬ p423)) : p1140 ∨ (¬ p224) ∨ p124 ∨ p344 ∨ (¬ p88) ∨ p6 ∨ (¬ p261) ∨ (¬ p423) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
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
  have u7 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p39 := by
    exact h35495
  rcases h31100 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u7)

theorem step36496 (p2 p11 p39 p68 p88 p124 p258 p261 p389 p419 : Prop)
    (h35495 : p39)
    (h31101 : p124 ∨ (¬ p11) ∨ (¬ p88) ∨ p2 ∨ p419 ∨ (¬ p39) ∨ (¬ p389) ∨ (¬ p68) ∨ p258 ∨ (¬ p261)) : (¬ p88) ∨ (¬ p11) ∨ p124 ∨ p2 ∨ p419 ∨ (¬ p389) ∨ (¬ p68) ∨ p258 ∨ (¬ p261) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p39 := by
    exact h35495
  rcases h31101 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)
  · exact False.elim (u3 q3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (u7 q8)
  · exact False.elim (q9 u8)

theorem step36497 (p17 p39 p88 p126 p423 p438 p1035 p1335 : Prop)
    (h35495 : p39)
    (h31102 : (¬ p1035) ∨ p126 ∨ (¬ p423) ∨ (¬ p39) ∨ (¬ p438) ∨ (¬ p1335) ∨ (¬ p88) ∨ (¬ p17)) : (¬ p423) ∨ p126 ∨ (¬ p1035) ∨ (¬ p438) ∨ (¬ p1335) ∨ (¬ p88) ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1335 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p39 := by
    exact h35495
  rcases h31102 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step36498 (p2 p17 p39 p68 p88 p258 p419 p1076 : Prop)
    (h35495 : p39)
    (h31103 : p419 ∨ (¬ p258) ∨ p2 ∨ (¬ p88) ∨ (¬ p1076) ∨ (¬ p17) ∨ (¬ p68) ∨ (¬ p39)) : p2 ∨ (¬ p258) ∨ p419 ∨ (¬ p88) ∨ (¬ p1076) ∨ (¬ p17) ∨ (¬ p68) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p2) := fun hu => hn (Or.inl hu)
  have u1 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p39 := by
    exact h35495
  rcases h31103 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u7)

theorem step36500 (p15 p39 p88 p124 p126 p258 p261 p595 p599 : Prop)
    (h35495 : p39)
    (h31105 : p124 ∨ p258 ∨ p15 ∨ p126 ∨ (¬ p39) ∨ (¬ p261) ∨ (¬ p595) ∨ (¬ p599) ∨ (¬ p88)) : p258 ∨ p124 ∨ p15 ∨ p126 ∨ (¬ p261) ∨ (¬ p595) ∨ (¬ p599) ∨ (¬ p88) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p258) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p126) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p261 := by
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
  have u7 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p39 := by
    exact h35495
  rcases h31105 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (u2 q2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step36501 (p15 p39 p88 p124 p224 p261 p303 p345 p595 p901 : Prop)
    (h35495 : p39)
    (h31107 : p124 ∨ p15 ∨ (¬ p88) ∨ (¬ p901) ∨ (¬ p261) ∨ (¬ p303) ∨ (¬ p39) ∨ p224 ∨ (¬ p595) ∨ (¬ p345)) : (¬ p88) ∨ p124 ∨ p15 ∨ (¬ p901) ∨ (¬ p261) ∨ (¬ p303) ∨ p224 ∨ (¬ p595) ∨ (¬ p345) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
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
  have u6 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p345 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p39 := by
    exact h35495
  rcases h31107 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u9)
  · exact False.elim (u6 q7)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step36502 (p12 p88 p225 p238 p347 p438 p1055 p1389 p1542 : Prop)
    (h35646 : p347)
    (h19485 : (¬ p12) ∨ (¬ p88) ∨ (¬ p225) ∨ (¬ p238) ∨ (¬ p347) ∨ (¬ p438) ∨ (¬ p1055) ∨ (¬ p1389) ∨ (¬ p1542)) : (¬ p1389) ∨ (¬ p1542) ∨ (¬ p238) ∨ (¬ p1055) ∨ (¬ p438) ∨ (¬ p12) ∨ (¬ p88) ∨ (¬ p225) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p347 := by
    exact h35646
  rcases h19485 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u0)
  · exact False.elim (q8 u1)

theorem step36503 (p6 p41 p87 p121 p187 p228 p789 p790 : Prop)
    (h35497 : p87)
    (h31111 : p790 ∨ p6 ∨ (¬ p187) ∨ (¬ p87) ∨ (¬ p121) ∨ (¬ p41) ∨ (¬ p228) ∨ p789) : (¬ p121) ∨ p790 ∨ p6 ∨ (¬ p187) ∨ (¬ p41) ∨ (¬ p228) ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p790) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p87 := by
    exact h35497
  rcases h31111 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (u6 q7)

theorem step36505 (p17 p87 p258 p580 p633 : Prop)
    (h35497 : p87)
    (h19260 : (¬ p17) ∨ (¬ p87) ∨ (¬ p258) ∨ (¬ p580) ∨ (¬ p633)) : (¬ p633) ∨ (¬ p580) ∨ (¬ p258) ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p580 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p87 := by
    exact h35497
  rcases h19260 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)

theorem step36506 (p3 p41 p87 p163 p188 : Prop)
    (h35497 : p87)
    (h31113 : p3 ∨ (¬ p41) ∨ (¬ p163) ∨ (¬ p87) ∨ (¬ p188)) : (¬ p163) ∨ p3 ∨ (¬ p41) ∨ (¬ p188) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p87 := by
    exact h35497
  rcases h31113 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)

theorem step36507 (p17 p87 p158 p303 p420 p579 p665 p918 p1055 : Prop)
    (h35497 : p87)
    (h31114 : (¬ p420) ∨ p1055 ∨ (¬ p579) ∨ (¬ p87) ∨ p918 ∨ (¬ p303) ∨ (¬ p158) ∨ (¬ p17) ∨ (¬ p665)) : (¬ p420) ∨ p1055 ∨ (¬ p579) ∨ p918 ∨ (¬ p303) ∨ (¬ p158) ∨ (¬ p17) ∨ (¬ p665) := by
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
  have u3 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p87 := by
    exact h35497
  rcases h31114 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u8)
  · exact False.elim (u3 q4)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step36508 (p6 p41 p87 p101 p185 p187 p224 p897 p926 : Prop)
    (h35497 : p87)
    (h31115 : (¬ p185) ∨ p6 ∨ p101 ∨ (¬ p41) ∨ (¬ p187) ∨ (¬ p926) ∨ (¬ p224) ∨ (¬ p87) ∨ (¬ p897)) : p101 ∨ (¬ p185) ∨ p6 ∨ (¬ p41) ∨ (¬ p187) ∨ (¬ p926) ∨ (¬ p224) ∨ (¬ p897) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p101) := fun hu => hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
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
  have u7 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p87 := by
    exact h35497
  rcases h31115 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u1)
  · exact False.elim (u2 q1)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u7)

theorem step36509 (p17 p87 p158 p224 p351 p382 p420 p579 p680 p918 : Prop)
    (h35497 : p87)
    (h31116 : p382 ∨ (¬ p420) ∨ (¬ p17) ∨ (¬ p158) ∨ (¬ p87) ∨ (¬ p680) ∨ p918 ∨ (¬ p579) ∨ (¬ p351) ∨ (¬ p224)) : p382 ∨ (¬ p420) ∨ (¬ p17) ∨ (¬ p158) ∨ (¬ p680) ∨ p918 ∨ (¬ p579) ∨ (¬ p351) ∨ (¬ p224) := by
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
  have u4 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p579 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p87 := by
    exact h35497
  rcases h31116 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step36510 (p17 p87 p382 p579 p633 p816 p1076 p1385 : Prop)
    (h35497 : p87)
    (h31117 : (¬ p579) ∨ p633 ∨ (¬ p17) ∨ (¬ p87) ∨ (¬ p816) ∨ p1385 ∨ p382 ∨ (¬ p1076)) : p633 ∨ (¬ p579) ∨ (¬ p17) ∨ (¬ p816) ∨ p1385 ∨ p382 ∨ (¬ p1076) := by
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
  have u3 : p816 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p87 := by
    exact h35497
  rcases h31117 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u3)
  · exact False.elim (u4 q5)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u6)

theorem step36511 (p8 p17 p87 p106 p158 p225 p579 p633 p918 : Prop)
    (h35497 : p87)
    (h31118 : p633 ∨ (¬ p579) ∨ (¬ p17) ∨ (¬ p158) ∨ (¬ p8) ∨ (¬ p225) ∨ p918 ∨ (¬ p87) ∨ (¬ p106)) : p633 ∨ (¬ p579) ∨ (¬ p17) ∨ (¬ p158) ∨ (¬ p8) ∨ (¬ p225) ∨ p918 ∨ (¬ p106) := by
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
  have u7 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p87 := by
    exact h35497
  rcases h31118 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u7)

theorem step36512 (p8 p17 p87 p158 p224 p389 p455 p579 p918 : Prop)
    (h35497 : p87)
    (h31119 : p455 ∨ (¬ p579) ∨ (¬ p8) ∨ p224 ∨ (¬ p87) ∨ (¬ p389) ∨ p918 ∨ (¬ p17) ∨ (¬ p158)) : p455 ∨ (¬ p579) ∨ (¬ p8) ∨ p224 ∨ (¬ p389) ∨ p918 ∨ (¬ p17) ∨ (¬ p158) := by
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
  have u4 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p87 := by
    exact h35497
  rcases h31119 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step36513 (p41 p87 p187 p1000 p1140 p1325 p1349 p1489 : Prop)
    (h35497 : p87)
    (h31120 : (¬ p41) ∨ (¬ p1349) ∨ (¬ p1489) ∨ p1325 ∨ (¬ p187) ∨ (¬ p1140) ∨ (¬ p87) ∨ (¬ p1000)) : (¬ p1140) ∨ (¬ p1349) ∨ (¬ p1489) ∨ p1325 ∨ (¬ p187) ∨ (¬ p41) ∨ (¬ p1000) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1140 := by
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
  have u5 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p87 := by
    exact h35497
  rcases h31120 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u6)

theorem step36514 (p41 p87 p188 p422 p1140 : Prop)
    (h35497 : p87)
    (h31121 : p1140 ∨ (¬ p41) ∨ p422 ∨ (¬ p87) ∨ (¬ p188)) : p1140 ∨ p422 ∨ (¬ p41) ∨ (¬ p188) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p422) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p87 := by
    exact h35497
  rcases h31121 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)

theorem step36515 (p87 p185 p419 p542 p789 p897 p926 p1385 : Prop)
    (h35497 : p87)
    (h31122 : (¬ p789) ∨ p1385 ∨ (¬ p926) ∨ (¬ p419) ∨ (¬ p542) ∨ (¬ p185) ∨ (¬ p87) ∨ (¬ p897)) : p1385 ∨ (¬ p926) ∨ (¬ p789) ∨ (¬ p419) ∨ (¬ p542) ∨ (¬ p185) ∨ (¬ p897) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1385) := fun hu => hn (Or.inl hu)
  have u1 : p926 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p789 := by
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
  have u6 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p87 := by
    exact h35497
  rcases h31122 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u6)

theorem step36516 (p87 p185 p224 p227 p228 p262 p576 p836 : Prop)
    (h35497 : p87)
    (h31123 : (¬ p836) ∨ p576 ∨ (¬ p224) ∨ (¬ p87) ∨ (¬ p228) ∨ (¬ p227) ∨ (¬ p262) ∨ (¬ p185)) : (¬ p836) ∨ p576 ∨ (¬ p224) ∨ (¬ p228) ∨ (¬ p227) ∨ (¬ p262) ∨ (¬ p185) := by
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
  have u3 : p228 := by
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
  have u6 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p87 := by
    exact h35497
  rcases h31123 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step36518 (p87 p124 p262 p576 p665 p789 p790 p1076 : Prop)
    (h35497 : p87)
    (h31125 : p1076 ∨ p576 ∨ (¬ p665) ∨ p789 ∨ (¬ p124) ∨ (¬ p87) ∨ p790 ∨ (¬ p262)) : p576 ∨ (¬ p665) ∨ p1076 ∨ p789 ∨ (¬ p124) ∨ p790 ∨ (¬ p262) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p576) := fun hu => hn (Or.inl hu)
  have u1 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p87 := by
    exact h35497
  rcases h31125 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u7)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u6)

theorem step36519 (p87 p125 p185 p262 p303 p576 p1115 : Prop)
    (h35497 : p87)
    (h31126 : (¬ p1115) ∨ p576 ∨ (¬ p87) ∨ p125 ∨ (¬ p262) ∨ (¬ p185) ∨ p303) : (¬ p1115) ∨ p576 ∨ p125 ∨ (¬ p262) ∨ (¬ p185) ∨ p303 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p87 := by
    exact h35497
  rcases h31126 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (u2 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)

theorem step36520 (p87 p125 p185 p225 p262 p434 p576 p836 : Prop)
    (h35497 : p87)
    (h31127 : (¬ p434) ∨ (¬ p836) ∨ p576 ∨ (¬ p262) ∨ p225 ∨ (¬ p87) ∨ (¬ p185) ∨ p125) : (¬ p836) ∨ (¬ p434) ∨ p576 ∨ (¬ p262) ∨ p225 ∨ (¬ p185) ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p87 := by
    exact h35497
  rcases h31127 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u5)
  · exact False.elim (u6 q7)

theorem step36521 (p87 p185 p262 p303 p347 p368 p382 p576 p897 p926 : Prop)
    (h35497 : p87)
    (h35646 : p347)
    (h31128 : p382 ∨ p576 ∨ (¬ p185) ∨ (¬ p926) ∨ (¬ p87) ∨ (¬ p897) ∨ (¬ p347) ∨ (¬ p368) ∨ (¬ p262) ∨ (¬ p303)) : p382 ∨ p576 ∨ (¬ p185) ∨ (¬ p926) ∨ (¬ p897) ∨ (¬ p368) ∨ (¬ p262) ∨ (¬ p303) := by
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
  have u4 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p87 := by
    exact h35497
  have u9 : p347 := by
    exact h35646
  rcases h31128 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)

theorem step36522 (p2 p87 p158 p303 p327 p556 p789 p790 p918 : Prop)
    (h35549 : p327)
    (h35497 : p87)
    (h31129 : (¬ p556) ∨ p918 ∨ (¬ p158) ∨ p303 ∨ (¬ p327) ∨ p790 ∨ (¬ p87) ∨ p789 ∨ p2) : p303 ∨ p918 ∨ (¬ p158) ∨ (¬ p556) ∨ p790 ∨ p789 ∨ p2 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p556 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p327 := by
    exact h35549
  have u8 : p87 := by
    exact h35497
  rcases h31129 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u3)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u7)
  · exact False.elim (u4 q5)
  · exact False.elim (q6 u8)
  · exact False.elim (u5 q7)
  · exact False.elim (u6 q8)

theorem step36523 (p87 p261 p576 p1624 p1651 : Prop)
    (h35497 : p87)
    (h31130 : (¬ p1651) ∨ (¬ p1624) ∨ (¬ p261) ∨ (¬ p87) ∨ p576) : (¬ p1651) ∨ (¬ p1624) ∨ (¬ p261) ∨ p576 := by
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
  have u3 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p87 := by
    exact h35497
  rcases h31130 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (u3 q4)

theorem step36524 (p87 p382 p519 p576 p789 p815 : Prop)
    (h35497 : p87)
    (h31131 : (¬ p789) ∨ p576 ∨ (¬ p382) ∨ (¬ p87) ∨ (¬ p519) ∨ (¬ p815)) : (¬ p382) ∨ p576 ∨ (¬ p789) ∨ (¬ p519) ∨ (¬ p815) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p519 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p815 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p87 := by
    exact h35497
  rcases h31131 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step36525 (p87 p125 p126 p261 p576 : Prop)
    (h35497 : p87)
    (h31132 : p576 ∨ (¬ p125) ∨ (¬ p87) ∨ (¬ p126) ∨ (¬ p261)) : (¬ p126) ∨ (¬ p125) ∨ p576 ∨ (¬ p261) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p87 := by
    exact h35497
  rcases h31132 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u3)

theorem step36527 (p3 p41 p87 p185 p187 p225 p664 p1115 : Prop)
    (h35497 : p87)
    (h35502 : p664)
    (h31134 : p225 ∨ (¬ p41) ∨ (¬ p1115) ∨ (¬ p187) ∨ (¬ p185) ∨ (¬ p3) ∨ (¬ p87) ∨ (¬ p664)) : (¬ p1115) ∨ p225 ∨ (¬ p41) ∨ (¬ p187) ∨ (¬ p185) ∨ (¬ p3) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p41 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p87 := by
    exact h35497
  have u7 : p664 := by
    exact h35502
  rcases h31134 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u7)

theorem step36528 (p3 p41 p87 p106 p185 p187 p1076 p1115 : Prop)
    (h35497 : p87)
    (h31135 : (¬ p1115) ∨ p1076 ∨ (¬ p185) ∨ (¬ p187) ∨ (¬ p3) ∨ (¬ p106) ∨ (¬ p41) ∨ (¬ p87)) : (¬ p1115) ∨ (¬ p185) ∨ p1076 ∨ (¬ p187) ∨ (¬ p3) ∨ (¬ p106) ∨ (¬ p41) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p87 := by
    exact h35497
  rcases h31135 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u7)

theorem step36529 (p87 p124 p258 p261 p576 : Prop)
    (h35497 : p87)
    (h31136 : p576 ∨ p124 ∨ p258 ∨ (¬ p261) ∨ (¬ p87)) : p258 ∨ p124 ∨ p576 ∨ (¬ p261) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p258) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p87 := by
    exact h35497
  rcases h31136 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)

theorem step36531 (p2 p17 p41 p87 p187 p389 p419 p455 p579 : Prop)
    (h35497 : p87)
    (h31138 : (¬ p389) ∨ (¬ p579) ∨ (¬ p87) ∨ p455 ∨ (¬ p187) ∨ p419 ∨ p2 ∨ (¬ p41) ∨ (¬ p17)) : p455 ∨ (¬ p389) ∨ (¬ p579) ∨ (¬ p187) ∨ p419 ∨ p2 ∨ (¬ p41) ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p579 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p87 := by
    exact h35497
  rcases h31138 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u8)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (u4 q5)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step36532 (p8 p87 p101 p121 p158 p224 p261 p918 p961 : Prop)
    (h35497 : p87)
    (h31139 : (¬ p101) ∨ (¬ p961) ∨ (¬ p261) ∨ (¬ p158) ∨ p224 ∨ (¬ p8) ∨ (¬ p121) ∨ p918 ∨ (¬ p87)) : (¬ p961) ∨ (¬ p158) ∨ (¬ p261) ∨ (¬ p101) ∨ p224 ∨ (¬ p8) ∨ (¬ p121) ∨ p918 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p101 := by
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
  have u7 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p87 := by
    exact h35497
  rcases h31139 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (u4 q4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)
  · exact False.elim (u7 q7)
  · exact False.elim (q8 u8)

theorem step36533 (p8 p87 p158 p189 p224 p422 p918 p1004 : Prop)
    (h35497 : p87)
    (h31140 : (¬ p422) ∨ (¬ p1004) ∨ (¬ p158) ∨ (¬ p8) ∨ (¬ p87) ∨ p918 ∨ p224 ∨ (¬ p189)) : (¬ p422) ∨ (¬ p189) ∨ (¬ p158) ∨ (¬ p8) ∨ p918 ∨ p224 ∨ (¬ p1004) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p189 := by
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
  have u4 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p87 := by
    exact h35497
  rcases h31140 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u7)
  · exact False.elim (u4 q5)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u1)

theorem step36534 (p87 p124 p185 p262 p344 p576 p664 p1115 : Prop)
    (h35502 : p664)
    (h35497 : p87)
    (h31141 : (¬ p1115) ∨ (¬ p344) ∨ (¬ p664) ∨ p576 ∨ (¬ p185) ∨ (¬ p124) ∨ (¬ p262) ∨ (¬ p87)) : (¬ p1115) ∨ (¬ p344) ∨ p576 ∨ (¬ p185) ∨ (¬ p124) ∨ (¬ p262) := by
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
  have u2 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p664 := by
    exact h35502
  have u7 : p87 := by
    exact h35497
  rcases h31141 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (u2 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u7)

theorem step36535 (p87 p124 p185 p262 p576 p668 p897 p926 p1076 : Prop)
    (h35497 : p87)
    (h35527 : p668)
    (h31142 : (¬ p926) ∨ p576 ∨ (¬ p262) ∨ (¬ p185) ∨ (¬ p87) ∨ p1076 ∨ (¬ p897) ∨ (¬ p668) ∨ (¬ p124)) : p576 ∨ (¬ p926) ∨ (¬ p262) ∨ (¬ p185) ∨ p1076 ∨ (¬ p897) ∨ (¬ p124) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p576) := fun hu => hn (Or.inl hu)
  have u1 : p926 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p87 := by
    exact h35497
  have u8 : p668 := by
    exact h35527
  rcases h31142 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u7)
  · exact False.elim (u4 q5)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u6)

theorem step36536 (p41 p87 p185 p187 p224 p897 p926 p1000 p1140 : Prop)
    (h35497 : p87)
    (h17062 : (¬ p41) ∨ (¬ p87) ∨ (¬ p185) ∨ (¬ p187) ∨ (¬ p224) ∨ (¬ p897) ∨ (¬ p926) ∨ (¬ p1000) ∨ (¬ p1140)) : (¬ p1140) ∨ (¬ p926) ∨ (¬ p1000) ∨ (¬ p41) ∨ (¬ p224) ∨ (¬ p185) ∨ (¬ p897) ∨ (¬ p187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p926 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p87 := by
    exact h35497
  rcases h17062 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u2)
  · exact False.elim (q8 u0)

theorem step36537 (p87 p382 p789 p815 p1385 : Prop)
    (h35497 : p87)
    (h31143 : (¬ p789) ∨ p1385 ∨ (¬ p87) ∨ (¬ p382) ∨ (¬ p815)) : p1385 ∨ (¬ p382) ∨ (¬ p789) ∨ (¬ p815) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1385) := fun hu => hn (Or.inl hu)
  have u1 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p815 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p87 := by
    exact h35497
  rcases h31143 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)

theorem step36538 (p8 p14 p47 p87 p110 p158 p189 p344 p918 : Prop)
    (h35497 : p87)
    (h31144 : p14 ∨ p918 ∨ (¬ p189) ∨ p344 ∨ (¬ p158) ∨ (¬ p47) ∨ (¬ p87) ∨ (¬ p8) ∨ (¬ p110)) : p14 ∨ p918 ∨ (¬ p189) ∨ p344 ∨ (¬ p158) ∨ (¬ p47) ∨ (¬ p8) ∨ (¬ p110) := by
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
  have u6 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p87 := by
    exact h35497
  rcases h31144 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step36540 (p41 p83 p189 p495 p582 : Prop)
    (h35574 : p582)
    (h31157 : p495 ∨ (¬ p41) ∨ (¬ p189) ∨ (¬ p83) ∨ (¬ p582)) : (¬ p189) ∨ p495 ∨ (¬ p41) ∨ (¬ p83) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p582 := by
    exact h35574
  rcases h31157 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)

theorem step36541 (p6 p10 p224 p347 p595 p1287 : Prop)
    (h35646 : p347)
    (h31166 : (¬ p347) ∨ p6 ∨ p224 ∨ p10 ∨ (¬ p1287) ∨ p595) : p10 ∨ p6 ∨ p224 ∨ (¬ p1287) ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p10) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p347 := by
    exact h35646
  rcases h31166 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u1 q1)
  · exact False.elim (u2 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (u4 q5)

#print axioms step36541

end NineRUPTrial
