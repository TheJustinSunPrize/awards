import Mathlib.Tactic.Tauto

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

namespace NineRUPTrial

theorem step24186 (p10 p108 p342 p534 p726 : Prop)
    (h24104 : p342)
    (h18000 : (¬ p10) ∨ (¬ p108) ∨ (¬ p342) ∨ (¬ p534) ∨ (¬ p726)) : (¬ p534) ∨ (¬ p10) ∨ (¬ p726) ∨ (¬ p108) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p342 := by
    exact h24104
  rcases h18000 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u2)

theorem step24187 (p125 p227 p342 p456 p633 : Prop)
    (h24104 : p342)
    (h19761 : (¬ p125) ∨ (¬ p227) ∨ (¬ p342) ∨ (¬ p456) ∨ (¬ p633)) : (¬ p125) ∨ (¬ p633) ∨ (¬ p227) ∨ (¬ p456) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p342 := by
    exact h24104
  rcases h19761 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)

theorem step24188 (p125 p310 p342 p1061 p1076 : Prop)
    (h24104 : p342)
    (h16243 : (¬ p125) ∨ (¬ p310) ∨ (¬ p342) ∨ (¬ p1061) ∨ (¬ p1076)) : (¬ p1061) ∨ (¬ p1076) ∨ (¬ p125) ∨ (¬ p310) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p342 := by
    exact h24104
  rcases h16243 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)

theorem step24189 (p342 p420 p640 p1076 p1095 : Prop)
    (h24104 : p342)
    (h17116 : (¬ p342) ∨ (¬ p420) ∨ (¬ p640) ∨ (¬ p1076) ∨ (¬ p1095)) : (¬ p640) ∨ (¬ p1095) ∨ (¬ p420) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p640 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p342 := by
    exact h24104
  rcases h17116 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)

theorem step24190 (p309 p342 p420 p640 p1055 p1095 : Prop)
    (h24104 : p342)
    (h17373 : (¬ p309) ∨ (¬ p342) ∨ (¬ p420) ∨ (¬ p640) ∨ (¬ p1055) ∨ (¬ p1095)) : (¬ p1095) ∨ (¬ p640) ∨ (¬ p420) ∨ (¬ p309) ∨ (¬ p1055) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p640 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p420 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p342 := by
    exact h24104
  rcases h17373 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u0)

theorem step24191 (p107 p287 p301 p342 p537 p940 : Prop)
    (h24104 : p342)
    (h19672 : (¬ p107) ∨ (¬ p287) ∨ (¬ p301) ∨ (¬ p342) ∨ (¬ p537) ∨ (¬ p940)) : (¬ p537) ∨ (¬ p940) ∨ (¬ p107) ∨ (¬ p301) ∨ (¬ p287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p107 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p342 := by
    exact h24104
  rcases h19672 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u1)

theorem step24194 (p102 p324 p342 p364 p406 p419 : Prop)
    (h24104 : p342)
    (h16227 : (¬ p102) ∨ (¬ p324) ∨ (¬ p342) ∨ (¬ p364) ∨ (¬ p406) ∨ (¬ p419)) : (¬ p364) ∨ (¬ p324) ∨ (¬ p102) ∨ (¬ p419) ∨ (¬ p406) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p364 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p324 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p342 := by
    exact h24104
  rcases h16227 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step24196 (p102 p324 p342 p434 p435 : Prop)
    (h24104 : p342)
    (h16791 : (¬ p102) ∨ (¬ p324) ∨ (¬ p342) ∨ (¬ p434) ∨ (¬ p435)) : (¬ p434) ∨ (¬ p324) ∨ (¬ p102) ∨ (¬ p435) := by
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
  have u2 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p342 := by
    exact h24104
  rcases h16791 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u3)

theorem step24197 (p288 p342 p515 p581 p1385 : Prop)
    (h24104 : p342)
    (h17368 : (¬ p288) ∨ (¬ p342) ∨ (¬ p515) ∨ (¬ p581) ∨ (¬ p1385)) : (¬ p515) ∨ (¬ p1385) ∨ (¬ p288) ∨ (¬ p581) := by
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
  have u2 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p342 := by
    exact h24104
  rcases h17368 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)

theorem step24215 (p102 p140 p256 p342 p515 p814 : Prop)
    (h24104 : p342)
    (h20429 : (¬ p102) ∨ (¬ p140) ∨ (¬ p256) ∨ (¬ p342) ∨ (¬ p515) ∨ (¬ p814)) : (¬ p140) ∨ (¬ p515) ∨ (¬ p256) ∨ (¬ p102) ∨ (¬ p814) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p515 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p256 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p342 := by
    exact h24104
  rcases h20429 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u4)

theorem step24216 (p342 p420 p462 p532 p1078 p1225 : Prop)
    (h24104 : p342)
    (h18022 : (¬ p342) ∨ (¬ p420) ∨ (¬ p462) ∨ (¬ p532) ∨ (¬ p1078) ∨ (¬ p1225)) : (¬ p462) ∨ (¬ p420) ∨ (¬ p1078) ∨ (¬ p1225) ∨ (¬ p532) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p462 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1078 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p342 := by
    exact h24104
  rcases h18022 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step24217 (p342 p386 p1080 : Prop)
    (h24104 : p342)
    (h12994 : (¬ p342) ∨ (¬ p386) ∨ p1080) : p1080 ∨ (¬ p386) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1080) := fun hu => hn (Or.inl hu)
  have u1 : p386 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p342 := by
    exact h24104
  rcases h12994 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (u0 q2)

theorem step24218 (p342 p364 p406 p594 p633 p1287 : Prop)
    (h24104 : p342)
    (h20594 : (¬ p342) ∨ (¬ p364) ∨ (¬ p406) ∨ (¬ p594) ∨ (¬ p633) ∨ (¬ p1287)) : (¬ p364) ∨ (¬ p594) ∨ (¬ p406) ∨ (¬ p1287) ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p364 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p594 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p342 := by
    exact h24104
  rcases h20594 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step24219 (p342 p364 p594 p633 p687 p1545 : Prop)
    (h24104 : p342)
    (h19627 : (¬ p342) ∨ (¬ p364) ∨ (¬ p594) ∨ (¬ p633) ∨ (¬ p687) ∨ (¬ p1545)) : (¬ p364) ∨ (¬ p687) ∨ (¬ p1545) ∨ (¬ p633) ∨ (¬ p594) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p364 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p594 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p342 := by
    exact h24104
  rcases h19627 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)

theorem step24220 (p342 p382 p387 p594 p619 p633 : Prop)
    (h24104 : p342)
    (h16718 : (¬ p342) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p594) ∨ (¬ p619) ∨ (¬ p633)) : (¬ p633) ∨ (¬ p619) ∨ (¬ p382) ∨ (¬ p594) ∨ (¬ p387) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p619 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p594 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p342 := by
    exact h24104
  rcases h16718 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u0)

theorem step24221 (p124 p262 p342 p515 p581 p1385 : Prop)
    (h24104 : p342)
    (h19633 : (¬ p124) ∨ (¬ p262) ∨ (¬ p342) ∨ (¬ p515) ∨ (¬ p581) ∨ (¬ p1385)) : (¬ p515) ∨ (¬ p1385) ∨ (¬ p124) ∨ (¬ p581) ∨ (¬ p262) := by
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
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p342 := by
    exact h24104
  rcases h19633 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u1)

theorem step24223 (p2 p6 p102 p342 : Prop)
    (h24104 : p342)
    (h24047 : p6 ∨ (¬ p342) ∨ (¬ p102) ∨ (¬ p2)) : p6 ∨ (¬ p102) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p6) := fun hu => hn (Or.inl hu)
  have u1 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p342 := by
    exact h24104
  rcases h24047 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)

theorem step24224 (p124 p303 p342 p382 : Prop)
    (h24104 : p342)
    (h24054 : p303 ∨ (¬ p342) ∨ (¬ p124) ∨ (¬ p382)) : p303 ∨ (¬ p124) ∨ (¬ p382) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p342 := by
    exact h24104
  rcases h24054 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)

theorem step24226 (p102 p105 p111 p112 p113 p114 p115 p120 : Prop)
    (h624 : p111 ∨ p120)
    (h629 : p112 ∨ p120)
    (h634 : p113 ∨ p120)
    (h639 : p114 ∨ p120)
    (h644 : p115 ∨ p120)
    (h537 : p102 ∨ p105 ∨ (¬ p111) ∨ (¬ p112) ∨ (¬ p113) ∨ (¬ p114) ∨ (¬ p115)) : p120 ∨ p102 ∨ p105 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p120) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p102) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p105) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p111 := by
    rcases h624 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p112 := by
    rcases h629 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p113 := by
    rcases h634 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p114 := by
    rcases h639 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p115 := by
    rcases h644 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h537 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24229 (p102 p105 p115 p116 p117 p118 p119 p120 : Prop)
    (h24226 : p120 ∨ p102 ∨ p105)
    (h640 : p115 ∨ p116)
    (h641 : p115 ∨ p117)
    (h642 : p115 ∨ p118)
    (h643 : p115 ∨ p119)
    (h562 : p102 ∨ p105 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p115 ∨ p102 ∨ p105 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p115) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p102) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p105) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p120 := by
    rcases h24226 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p116 := by
    rcases h640 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p117 := by
    rcases h641 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p118 := by
    rcases h642 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p119 := by
    rcases h643 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h562 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step24230 (p102 p105 p111 p116 p117 p118 p119 p120 : Prop)
    (h24226 : p120 ∨ p102 ∨ p105)
    (h620 : p111 ∨ p116)
    (h621 : p111 ∨ p117)
    (h622 : p111 ∨ p118)
    (h623 : p111 ∨ p119)
    (h562 : p102 ∨ p105 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p111 ∨ p102 ∨ p105 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p111) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p102) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p105) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p120 := by
    rcases h24226 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p116 := by
    rcases h620 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p117 := by
    rcases h621 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p118 := by
    rcases h622 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p119 := by
    rcases h623 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h562 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step24231 (p102 p105 p112 p116 p117 p118 p119 p120 : Prop)
    (h24226 : p120 ∨ p102 ∨ p105)
    (h625 : p112 ∨ p116)
    (h626 : p112 ∨ p117)
    (h627 : p112 ∨ p118)
    (h628 : p112 ∨ p119)
    (h562 : p102 ∨ p105 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p112 ∨ p102 ∨ p105 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p112) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p102) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p105) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p120 := by
    rcases h24226 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p116 := by
    rcases h625 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p117 := by
    rcases h626 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p118 := by
    rcases h627 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p119 := by
    rcases h628 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h562 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step24232 (p102 p105 p113 p116 p117 p118 p119 p120 : Prop)
    (h24226 : p120 ∨ p102 ∨ p105)
    (h630 : p113 ∨ p116)
    (h631 : p113 ∨ p117)
    (h632 : p113 ∨ p118)
    (h633 : p113 ∨ p119)
    (h562 : p102 ∨ p105 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p113 ∨ p102 ∨ p105 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p113) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p102) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p105) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p120 := by
    rcases h24226 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p116 := by
    rcases h630 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p117 := by
    rcases h631 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p118 := by
    rcases h632 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p119 := by
    rcases h633 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h562 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step24233 (p102 p105 p111 p112 p113 p114 p115 p116 p117 p118 p119 p120 : Prop)
    (h24226 : p120 ∨ p102 ∨ p105)
    (h24229 : p115 ∨ p102 ∨ p105)
    (h24230 : p111 ∨ p102 ∨ p105)
    (h24231 : p112 ∨ p102 ∨ p105)
    (h24232 : p113 ∨ p102 ∨ p105)
    (h537 : p102 ∨ p105 ∨ (¬ p111) ∨ (¬ p112) ∨ (¬ p113) ∨ (¬ p114) ∨ (¬ p115))
    (h635 : p114 ∨ p116)
    (h636 : p114 ∨ p117)
    (h637 : p114 ∨ p118)
    (h638 : p114 ∨ p119)
    (h562 : p102 ∨ p105 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p102 ∨ p105 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p102) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p105) := fun hu => hn (Or.inr hu)
  have u2 : p120 := by
    rcases h24226 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p115 := by
    rcases h24229 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p111 := by
    rcases h24230 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p112 := by
    rcases h24231 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p113 := by
    rcases h24232 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p114) := by
    rcases h537 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u0 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u6)
    · exact q5
    · exact False.elim (q6 u3)
  have u8 : p116 := by
    rcases h635 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p117 := by
    rcases h636 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p118 := by
    rcases h637 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p119 := by
    rcases h638 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h562 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u2)

theorem step24234 (p420 p495 p499 p634 p639 p1096 : Prop)
    (h20942 : p495 ∨ p499)
    (h10764 : p499 ∨ (¬ p634) ∨ (¬ p1096))
    (h24170 : (¬ p639) ∨ (¬ p1096) ∨ (¬ p495) ∨ (¬ p420))
    (h20840 : p639 ∨ p634) : (¬ p1096) ∨ (¬ p420) ∨ p499 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p499) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p495 := by
    rcases h20942 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : (¬ p634) := by
    rcases h10764 with q0 | q1 | q2
    · exact False.elim (u2 q0)
    · exact q1
    · exact False.elim (q2 u0)
  have u5 : (¬ p639) := by
    rcases h24170 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u1)
  rcases h20840 with q0 | q1
  · exact False.elim (u5 q0)
  · exact False.elim (u4 q1)

theorem step24235 (p19 p102 p323 p325 p329 p1187 : Prop)
    (h12233 : (¬ p19) ∨ (¬ p329) ∨ (¬ p1187))
    (h24167 : (¬ p325) ∨ (¬ p19) ∨ (¬ p1187) ∨ (¬ p102))
    (h21607 : p329 ∨ p323 ∨ p325) : (¬ p1187) ∨ p323 ∨ (¬ p19) ∨ (¬ p102) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p323) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p329) := by
    rcases h12233 with q0 | q1 | q2
    · exact False.elim (q0 u2)
    · exact q1
    · exact False.elim (q2 u0)
  have u5 : (¬ p325) := by
    rcases h24167 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u0)
    · exact False.elim (q3 u3)
  rcases h21607 with q0 | q1 | q2
  · exact False.elim (u4 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (u5 q2)

theorem step24236 (p980 p981 p982 p983 p986 p987 p988 p989 p990 p991 p992 p993 p994 p995 : Prop)
    (h20747 : p982 ∨ p980)
    (h15106 : (¬ p980) ∨ (¬ p983))
    (h24138 : p987 ∨ p981 ∨ p982)
    (h24139 : p986 ∨ p981 ∨ p982)
    (h24140 : p990 ∨ p981 ∨ p982)
    (h24141 : p989 ∨ p981 ∨ p982)
    (h5729 : p981 ∨ p983 ∨ (¬ p986) ∨ (¬ p987) ∨ (¬ p988) ∨ (¬ p989) ∨ (¬ p990))
    (h5822 : p988 ∨ p991)
    (h5823 : p988 ∨ p992)
    (h5824 : p988 ∨ p993)
    (h5825 : p988 ∨ p994)
    (h5826 : p988 ∨ p995)
    (h5753 : p981 ∨ p982 ∨ (¬ p991) ∨ (¬ p992) ∨ (¬ p993) ∨ (¬ p994) ∨ (¬ p995)) : p981 ∨ p982 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p981) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p982) := fun hu => hn (Or.inr hu)
  have u2 : p980 := by
    rcases h20747 with q0 | q1
    · exact False.elim (u1 q0)
    · exact q1
  have u3 : (¬ p983) := by
    rcases h15106 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u4 : p987 := by
    rcases h24138 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p986 := by
    rcases h24139 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p990 := by
    rcases h24140 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : p989 := by
    rcases h24141 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u8 : (¬ p988) := by
    rcases h5729 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u0 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u4)
    · exact q4
    · exact False.elim (q5 u7)
    · exact False.elim (q6 u6)
  have u9 : p991 := by
    rcases h5822 with q0 | q1
    · exact False.elim (u8 q0)
    · exact q1
  have u10 : p992 := by
    rcases h5823 with q0 | q1
    · exact False.elim (u8 q0)
    · exact q1
  have u11 : p993 := by
    rcases h5824 with q0 | q1
    · exact False.elim (u8 q0)
    · exact q1
  have u12 : p994 := by
    rcases h5825 with q0 | q1
    · exact False.elim (u8 q0)
    · exact q1
  have u13 : p995 := by
    rcases h5826 with q0 | q1
    · exact False.elim (u8 q0)
    · exact q1
  rcases h5753 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u12)
  · exact False.elim (q6 u13)

theorem step24237 (p635 p642 p1076 p1096 p1099 p1229 p1306 p1310 : Prop)
    (h9367 : p1096 ∨ (¬ p1229) ∨ (¬ p1306))
    (h23090 : p1310 ∨ p1306)
    (h21802 : p1096 ∨ p1099)
    (h23354 : (¬ p1229) ∨ (¬ p642) ∨ p1096 ∨ (¬ p1076))
    (h8737 : (¬ p635) ∨ (¬ p1076) ∨ (¬ p1099) ∨ (¬ p1229) ∨ (¬ p1310))
    (h23006 : p642 ∨ p635) : (¬ p1076) ∨ p1096 ∨ (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1306) := by
    rcases h9367 with q0 | q1 | q2
    · exact False.elim (u1 q0)
    · exact False.elim (q1 u2)
    · exact q2
  have u4 : p1310 := by
    rcases h23090 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u5 : p1099 := by
    rcases h21802 with q0 | q1
    · exact False.elim (u1 q0)
    · exact q1
  have u6 : (¬ p642) := by
    rcases h23354 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u2)
    · exact q1
    · exact False.elim (u1 q2)
    · exact False.elim (q3 u0)
  have u7 : (¬ p635) := by
    rcases h8737 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u2)
    · exact False.elim (q4 u4)
  rcases h23006 with q0 | q1
  · exact False.elim (u6 q0)
  · exact False.elim (u7 q1)

theorem step24242 (p19 p102 p224 p323 p344 p387 p657 : Prop)
    (h17986 : (¬ p19) ∨ (¬ p102) ∨ (¬ p344) ∨ (¬ p657))
    (h17313 : (¬ p19) ∨ (¬ p224) ∨ (¬ p323) ∨ (¬ p387))
    (h20814 : p224 ∨ p657) : (¬ p19) ∨ (¬ p387) ∨ (¬ p323) ∨ (¬ p344) ∨ (¬ p102) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p657) := by
    rcases h17986 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u0)
    · exact False.elim (q1 u4)
    · exact False.elim (q2 u3)
    · exact q3
  have u6 : (¬ p224) := by
    rcases h17313 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (q2 u2)
    · exact False.elim (q3 u1)
  rcases h20814 with q0 | q1
  · exact False.elim (u6 q0)
  · exact False.elim (u5 q1)

theorem step24243 (p41 p63 p83 p88 p124 p189 p344 p496 p576 p657 : Prop)
    (h19503 : (¬ p41) ∨ (¬ p83) ∨ (¬ p124) ∨ (¬ p189) ∨ (¬ p344) ∨ (¬ p496) ∨ (¬ p576) ∨ (¬ p657))
    (h7048 : (¬ p41) ∨ (¬ p88) ∨ (¬ p189))
    (h23700 : p83 ∨ p88 ∨ p63) : (¬ p189) ∨ (¬ p41) ∨ p63 ∨ (¬ p576) ∨ (¬ p496) ∨ (¬ p657) ∨ (¬ p344) ∨ (¬ p124) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p657 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p83) := by
    rcases h19503 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
    · exact False.elim (q0 u1)
    · exact q1
    · exact False.elim (q2 u7)
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u6)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u3)
    · exact False.elim (q7 u5)
  have u9 : (¬ p88) := by
    rcases h7048 with q0 | q1 | q2
    · exact False.elim (q0 u1)
    · exact q1
    · exact False.elim (q2 u0)
  rcases h23700 with q0 | q1 | q2
  · exact False.elim (u8 q0)
  · exact False.elim (u9 q1)
  · exact False.elim (u2 q2)

theorem step24251 (p41 p44 p138 p141 p142 p234 p424 p576 p796 : Prop)
    (h11358 : (¬ p424) ∨ (¬ p796))
    (h11254 : (¬ p44) ∨ (¬ p234) ∨ (¬ p796))
    (h23672 : (¬ p234) ∨ (¬ p576) ∨ (¬ p138) ∨ (¬ p796) ∨ p424)
    (h23818 : p41 ∨ p44)
    (h16293 : p138 ∨ (¬ p142))
    (h7323 : (¬ p41) ∨ (¬ p141) ∨ (¬ p576))
    (h22892 : p138 ∨ p142 ∨ p141) : (¬ p796) ∨ (¬ p576) ∨ (¬ p234) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p424) := by
    rcases h11358 with q0 | q1
    · exact q0
    · exact False.elim (q1 u0)
  have u4 : (¬ p44) := by
    rcases h11254 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u0)
  have u5 : (¬ p138) := by
    rcases h23672 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u2)
    · exact False.elim (q1 u1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (u3 q4)
  have u6 : p41 := by
    rcases h23818 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u7 : (¬ p142) := by
    rcases h16293 with q0 | q1
    · exact False.elim (u5 q0)
    · exact q1
  have u8 : (¬ p141) := by
    rcases h7323 with q0 | q1 | q2
    · exact False.elim (q0 u6)
    · exact q1
    · exact False.elim (q2 u1)
  rcases h22892 with q0 | q1 | q2
  · exact False.elim (u5 q0)
  · exact False.elim (u7 q1)
  · exact False.elim (u8 q2)

theorem step24252 (p324 p330 p332 p333 p334 p335 p336 p340 : Prop)
    (h1802 : p332 ∨ p340)
    (h1807 : p333 ∨ p340)
    (h1812 : p334 ∨ p340)
    (h1817 : p335 ∨ p340)
    (h1822 : p336 ∨ p340)
    (h1702 : p324 ∨ p330 ∨ (¬ p332) ∨ (¬ p333) ∨ (¬ p334) ∨ (¬ p335) ∨ (¬ p336)) : p340 ∨ p330 ∨ p324 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p340) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p330) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p324) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p332 := by
    rcases h1802 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p333 := by
    rcases h1807 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p334 := by
    rcases h1812 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p335 := by
    rcases h1817 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p336 := by
    rcases h1822 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1702 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24253 (p324 p330 p332 p337 p338 p339 p340 p341 : Prop)
    (h24252 : p340 ∨ p330 ∨ p324)
    (h1799 : p332 ∨ p337)
    (h1800 : p332 ∨ p338)
    (h1801 : p332 ∨ p339)
    (h1803 : p332 ∨ p341)
    (h1727 : p324 ∨ p330 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341)) : p332 ∨ p330 ∨ p324 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p332) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p330) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p324) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p340 := by
    rcases h24252 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p337 := by
    rcases h1799 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p338 := by
    rcases h1800 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p339 := by
    rcases h1801 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p341 := by
    rcases h1803 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1727 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24254 (p324 p330 p333 p337 p338 p339 p340 p341 : Prop)
    (h24252 : p340 ∨ p330 ∨ p324)
    (h1804 : p333 ∨ p337)
    (h1805 : p333 ∨ p338)
    (h1806 : p333 ∨ p339)
    (h1808 : p333 ∨ p341)
    (h1727 : p324 ∨ p330 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341)) : p333 ∨ p330 ∨ p324 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p333) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p330) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p324) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p340 := by
    rcases h24252 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p337 := by
    rcases h1804 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p338 := by
    rcases h1805 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p339 := by
    rcases h1806 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p341 := by
    rcases h1808 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1727 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24255 (p324 p330 p334 p337 p338 p339 p340 p341 : Prop)
    (h24252 : p340 ∨ p330 ∨ p324)
    (h1809 : p334 ∨ p337)
    (h1810 : p334 ∨ p338)
    (h1811 : p334 ∨ p339)
    (h1813 : p334 ∨ p341)
    (h1727 : p324 ∨ p330 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341)) : p334 ∨ p330 ∨ p324 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p334) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p330) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p324) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p340 := by
    rcases h24252 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p337 := by
    rcases h1809 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p338 := by
    rcases h1810 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p339 := by
    rcases h1811 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p341 := by
    rcases h1813 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1727 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24256 (p324 p330 p335 p337 p338 p339 p340 p341 : Prop)
    (h24252 : p340 ∨ p330 ∨ p324)
    (h1814 : p335 ∨ p337)
    (h1815 : p335 ∨ p338)
    (h1816 : p335 ∨ p339)
    (h1818 : p335 ∨ p341)
    (h1727 : p324 ∨ p330 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341)) : p335 ∨ p330 ∨ p324 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p335) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p330) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p324) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p340 := by
    rcases h24252 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p337 := by
    rcases h1814 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p338 := by
    rcases h1815 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p339 := by
    rcases h1816 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p341 := by
    rcases h1818 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1727 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24257 (p324 p330 p332 p333 p334 p335 p336 p337 p338 p339 p340 p341 : Prop)
    (h24252 : p340 ∨ p330 ∨ p324)
    (h24253 : p332 ∨ p330 ∨ p324)
    (h24254 : p333 ∨ p330 ∨ p324)
    (h24255 : p334 ∨ p330 ∨ p324)
    (h24256 : p335 ∨ p330 ∨ p324)
    (h1702 : p324 ∨ p330 ∨ (¬ p332) ∨ (¬ p333) ∨ (¬ p334) ∨ (¬ p335) ∨ (¬ p336))
    (h1819 : p336 ∨ p337)
    (h1820 : p336 ∨ p338)
    (h1821 : p336 ∨ p339)
    (h1823 : p336 ∨ p341)
    (h1727 : p324 ∨ p330 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341)) : p330 ∨ p324 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p330) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p324) := fun hu => hn (Or.inr hu)
  have u2 : p340 := by
    rcases h24252 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p332 := by
    rcases h24253 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p333 := by
    rcases h24254 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p334 := by
    rcases h24255 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p335 := by
    rcases h24256 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p336) := by
    rcases h1702 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p337 := by
    rcases h1819 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p338 := by
    rcases h1820 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p339 := by
    rcases h1821 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p341 := by
    rcases h1823 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h1727 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u11)

theorem step24258 (p15 p17 p41 p44 p84 p89 p137 p193 p256 p330 p424 p576 : Prop)
    (h16815 : (¬ p17) ∨ (¬ p137) ∨ (¬ p193) ∨ (¬ p330) ∨ (¬ p424))
    (h16302 : (¬ p41) ∨ (¬ p137) ∨ (¬ p330) ∨ (¬ p424) ∨ (¬ p576))
    (h21276 : p256 ∨ p17)
    (h23818 : p41 ∨ p44)
    (h10747 : (¬ p84) ∨ (¬ p256) ∨ (¬ p576))
    (h13949 : p15 ∨ (¬ p44) ∨ (¬ p89) ∨ (¬ p193))
    (h22277 : p89 ∨ p84) : (¬ p137) ∨ (¬ p330) ∨ (¬ p424) ∨ (¬ p576) ∨ (¬ p193) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p137 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p17) := by
    rcases h16815 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u1)
    · exact False.elim (q4 u2)
  have u7 : (¬ p41) := by
    rcases h16302 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u2)
    · exact False.elim (q4 u3)
  have u8 : p256 := by
    rcases h21276 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p44 := by
    rcases h23818 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : (¬ p84) := by
    rcases h10747 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u8)
    · exact False.elim (q2 u3)
  have u11 : (¬ p89) := by
    rcases h13949 with q0 | q1 | q2 | q3
    · exact False.elim (u5 q0)
    · exact False.elim (q1 u9)
    · exact q2
    · exact False.elim (q3 u4)
  rcases h22277 with q0 | q1
  · exact False.elim (u11 q0)
  · exact False.elim (u10 q1)

theorem step24259 (p15 p17 p41 p44 p84 p89 p141 p189 p193 p256 p576 : Prop)
    (h6740 : (¬ p189) ∨ (¬ p193))
    (h14990 : (¬ p17) ∨ (¬ p141) ∨ p189)
    (h7323 : (¬ p41) ∨ (¬ p141) ∨ (¬ p576))
    (h21276 : p256 ∨ p17)
    (h23818 : p41 ∨ p44)
    (h10747 : (¬ p84) ∨ (¬ p256) ∨ (¬ p576))
    (h13949 : p15 ∨ (¬ p44) ∨ (¬ p89) ∨ (¬ p193))
    (h22277 : p89 ∨ p84) : (¬ p141) ∨ (¬ p576) ∨ (¬ p193) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p189) := by
    rcases h6740 with q0 | q1
    · exact q0
    · exact False.elim (q1 u2)
  have u5 : (¬ p17) := by
    rcases h14990 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u4 q2)
  have u6 : (¬ p41) := by
    rcases h7323 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u1)
  have u7 : p256 := by
    rcases h21276 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u8 : p44 := by
    rcases h23818 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : (¬ p84) := by
    rcases h10747 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u7)
    · exact False.elim (q2 u1)
  have u10 : (¬ p89) := by
    rcases h13949 with q0 | q1 | q2 | q3
    · exact False.elim (u3 q0)
    · exact False.elim (q1 u8)
    · exact q2
    · exact False.elim (q3 u2)
  rcases h22277 with q0 | q1
  · exact False.elim (u10 q0)
  · exact False.elim (u9 q1)

theorem step24260 (p15 p134 p137 p141 p142 p193 p234 p324 p330 p424 p576 p796 : Prop)
    (h24251 : (¬ p796) ∨ (¬ p576) ∨ (¬ p234))
    (h23744 : p424 ∨ p796)
    (h24259 : (¬ p141) ∨ (¬ p576) ∨ (¬ p193) ∨ p15)
    (h24112 : p141 ∨ p134)
    (h11275 : (¬ p134) ∨ (¬ p142))
    (h11517 : (¬ p134) ∨ (¬ p324) ∨ (¬ p424))
    (h22150 : p137 ∨ p141 ∨ p142)
    (h24257 : p330 ∨ p324)
    (h24258 : (¬ p137) ∨ (¬ p330) ∨ (¬ p424) ∨ (¬ p576) ∨ (¬ p193) ∨ p15) : (¬ p576) ∨ (¬ p193) ∨ (¬ p234) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p796) := by
    rcases h24251 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u2)
  have u5 : p424 := by
    rcases h23744 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u6 : (¬ p141) := by
    rcases h24259 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u1)
    · exact False.elim (u3 q3)
  have u7 : p134 := by
    rcases h24112 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : (¬ p142) := by
    rcases h11275 with q0 | q1
    · exact False.elim (q0 u7)
    · exact q1
  have u9 : (¬ p324) := by
    rcases h11517 with q0 | q1 | q2
    · exact False.elim (q0 u7)
    · exact q1
    · exact False.elim (q2 u5)
  have u10 : p137 := by
    rcases h22150 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u6 q1)
    · exact False.elim (u8 q2)
  have u11 : p330 := by
    rcases h24257 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h24258 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u11)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)
  · exact False.elim (u3 q5)

theorem step24262 (p14 p18 p69 p229 p879 p1096 : Prop)
    (h10795 : (¬ p69) ∨ (¬ p879) ∨ (¬ p1096))
    (h23014 : (¬ p18) ∨ p229 ∨ (¬ p69) ∨ (¬ p1096))
    (h23657 : p879 ∨ p14)
    (h12007 : (¬ p14) ∨ (¬ p229)) : (¬ p1096) ∨ (¬ p18) ∨ (¬ p69) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
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
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p879) := by
    rcases h10795 with q0 | q1 | q2
    · exact False.elim (q0 u2)
    · exact q1
    · exact False.elim (q2 u0)
  have u4 : p229 := by
    rcases h23014 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u1)
    · exact q1
    · exact False.elim (q2 u2)
    · exact False.elim (q3 u0)
  have u5 : p14 := by
    rcases h23657 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  rcases h12007 with q0 | q1
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)

theorem step24263 (p1206 p1213 p1215 p1216 p1217 p1218 p1219 p1223 : Prop)
    (h7301 : p1215 ∨ p1223)
    (h7306 : p1216 ∨ p1223)
    (h7311 : p1217 ∨ p1223)
    (h7316 : p1218 ∨ p1223)
    (h7321 : p1219 ∨ p1223)
    (h7211 : p1206 ∨ p1213 ∨ (¬ p1215) ∨ (¬ p1216) ∨ (¬ p1217) ∨ (¬ p1218) ∨ (¬ p1219)) : p1223 ∨ p1213 ∨ p1206 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1223) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1213) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1206) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1215 := by
    rcases h7301 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1216 := by
    rcases h7306 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1217 := by
    rcases h7311 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1218 := by
    rcases h7316 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1219 := by
    rcases h7321 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7211 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24264 (p1206 p1213 p1215 p1220 p1221 p1222 p1223 p1224 : Prop)
    (h24263 : p1223 ∨ p1213 ∨ p1206)
    (h7298 : p1215 ∨ p1220)
    (h7299 : p1215 ∨ p1221)
    (h7300 : p1215 ∨ p1222)
    (h7302 : p1215 ∨ p1224)
    (h7236 : p1206 ∨ p1213 ∨ (¬ p1220) ∨ (¬ p1221) ∨ (¬ p1222) ∨ (¬ p1223) ∨ (¬ p1224)) : p1215 ∨ p1213 ∨ p1206 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1215) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1213) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1206) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1223 := by
    rcases h24263 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1220 := by
    rcases h7298 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1221 := by
    rcases h7299 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1222 := by
    rcases h7300 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1224 := by
    rcases h7302 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7236 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24265 (p1206 p1213 p1216 p1220 p1221 p1222 p1223 p1224 : Prop)
    (h24263 : p1223 ∨ p1213 ∨ p1206)
    (h7303 : p1216 ∨ p1220)
    (h7304 : p1216 ∨ p1221)
    (h7305 : p1216 ∨ p1222)
    (h7307 : p1216 ∨ p1224)
    (h7236 : p1206 ∨ p1213 ∨ (¬ p1220) ∨ (¬ p1221) ∨ (¬ p1222) ∨ (¬ p1223) ∨ (¬ p1224)) : p1216 ∨ p1213 ∨ p1206 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1216) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1213) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1206) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1223 := by
    rcases h24263 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1220 := by
    rcases h7303 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1221 := by
    rcases h7304 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1222 := by
    rcases h7305 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1224 := by
    rcases h7307 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7236 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24266 (p1206 p1213 p1217 p1220 p1221 p1222 p1223 p1224 : Prop)
    (h24263 : p1223 ∨ p1213 ∨ p1206)
    (h7308 : p1217 ∨ p1220)
    (h7309 : p1217 ∨ p1221)
    (h7310 : p1217 ∨ p1222)
    (h7312 : p1217 ∨ p1224)
    (h7236 : p1206 ∨ p1213 ∨ (¬ p1220) ∨ (¬ p1221) ∨ (¬ p1222) ∨ (¬ p1223) ∨ (¬ p1224)) : p1217 ∨ p1213 ∨ p1206 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1217) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1213) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1206) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1223 := by
    rcases h24263 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1220 := by
    rcases h7308 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1221 := by
    rcases h7309 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1222 := by
    rcases h7310 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1224 := by
    rcases h7312 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7236 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24267 (p1206 p1213 p1218 p1220 p1221 p1222 p1223 p1224 : Prop)
    (h24263 : p1223 ∨ p1213 ∨ p1206)
    (h7313 : p1218 ∨ p1220)
    (h7314 : p1218 ∨ p1221)
    (h7315 : p1218 ∨ p1222)
    (h7317 : p1218 ∨ p1224)
    (h7236 : p1206 ∨ p1213 ∨ (¬ p1220) ∨ (¬ p1221) ∨ (¬ p1222) ∨ (¬ p1223) ∨ (¬ p1224)) : p1218 ∨ p1213 ∨ p1206 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1218) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1213) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1206) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1223 := by
    rcases h24263 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1220 := by
    rcases h7313 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1221 := by
    rcases h7314 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1222 := by
    rcases h7315 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1224 := by
    rcases h7317 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7236 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24268 (p1206 p1213 p1215 p1216 p1217 p1218 p1219 p1220 p1221 p1222 p1223 p1224 : Prop)
    (h24263 : p1223 ∨ p1213 ∨ p1206)
    (h24264 : p1215 ∨ p1213 ∨ p1206)
    (h24265 : p1216 ∨ p1213 ∨ p1206)
    (h24266 : p1217 ∨ p1213 ∨ p1206)
    (h24267 : p1218 ∨ p1213 ∨ p1206)
    (h7211 : p1206 ∨ p1213 ∨ (¬ p1215) ∨ (¬ p1216) ∨ (¬ p1217) ∨ (¬ p1218) ∨ (¬ p1219))
    (h7318 : p1219 ∨ p1220)
    (h7319 : p1219 ∨ p1221)
    (h7320 : p1219 ∨ p1222)
    (h7322 : p1219 ∨ p1224)
    (h7236 : p1206 ∨ p1213 ∨ (¬ p1220) ∨ (¬ p1221) ∨ (¬ p1222) ∨ (¬ p1223) ∨ (¬ p1224)) : p1213 ∨ p1206 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1213) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1206) := fun hu => hn (Or.inr hu)
  have u2 : p1223 := by
    rcases h24263 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1215 := by
    rcases h24264 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1216 := by
    rcases h24265 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1217 := by
    rcases h24266 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p1218 := by
    rcases h24267 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p1219) := by
    rcases h7211 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p1220 := by
    rcases h7318 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p1221 := by
    rcases h7319 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p1222 := by
    rcases h7320 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p1224 := by
    rcases h7322 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h7236 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u11)

theorem step24269 (p235 p423 p1141 p1145 p1149 p1150 p1151 p1152 p1153 p1154 p1155 p1156 p1157 p1158 : Prop)
    (h21560 : p1145 ∨ p1141)
    (h11243 : (¬ p423) ∨ (¬ p1141))
    (h22196 : p1149 ∨ p235 ∨ p423)
    (h22197 : p1153 ∨ p235 ∨ p423)
    (h22198 : p1152 ∨ p235 ∨ p423)
    (h22199 : p1151 ∨ p235 ∨ p423)
    (h6766 : p235 ∨ p423 ∨ (¬ p1149) ∨ (¬ p1150) ∨ (¬ p1151) ∨ (¬ p1152) ∨ (¬ p1153))
    (h6869 : p1150 ∨ p1154)
    (h6870 : p1150 ∨ p1155)
    (h6871 : p1150 ∨ p1156)
    (h6872 : p1150 ∨ p1157)
    (h6873 : p1150 ∨ p1158)
    (h6789 : p235 ∨ p1145 ∨ (¬ p1154) ∨ (¬ p1155) ∨ (¬ p1156) ∨ (¬ p1157) ∨ (¬ p1158)) : p1145 ∨ p235 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1145) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p235) := fun hu => hn (Or.inr hu)
  have u2 : p1141 := by
    rcases h21560 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : (¬ p423) := by
    rcases h11243 with q0 | q1
    · exact q0
    · exact False.elim (q1 u2)
  have u4 : p1149 := by
    rcases h22196 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u3 q2)
  have u5 : p1153 := by
    rcases h22197 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u3 q2)
  have u6 : p1152 := by
    rcases h22198 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u3 q2)
  have u7 : p1151 := by
    rcases h22199 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u3 q2)
  have u8 : (¬ p1150) := by
    rcases h6766 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact q3
    · exact False.elim (q4 u7)
    · exact False.elim (q5 u6)
    · exact False.elim (q6 u5)
  have u9 : p1154 := by
    rcases h6869 with q0 | q1
    · exact False.elim (u8 q0)
    · exact q1
  have u10 : p1155 := by
    rcases h6870 with q0 | q1
    · exact False.elim (u8 q0)
    · exact q1
  have u11 : p1156 := by
    rcases h6871 with q0 | q1
    · exact False.elim (u8 q0)
    · exact q1
  have u12 : p1157 := by
    rcases h6872 with q0 | q1
    · exact False.elim (u8 q0)
    · exact q1
  have u13 : p1158 := by
    rcases h6873 with q0 | q1
    · exact False.elim (u8 q0)
    · exact q1
  rcases h6789 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u12)
  · exact False.elim (q6 u13)

theorem step24270 (p235 p423 p1149 p1150 p1151 p1152 p1153 p1154 p1155 p1156 p1157 p1158 : Prop)
    (h6766 : p235 ∨ p423 ∨ (¬ p1149) ∨ (¬ p1150) ∨ (¬ p1151) ∨ (¬ p1152) ∨ (¬ p1153))
    (h6869 : p1150 ∨ p1154)
    (h6870 : p1150 ∨ p1155)
    (h6871 : p1150 ∨ p1156)
    (h6872 : p1150 ∨ p1157)
    (h6873 : p1150 ∨ p1158)
    (h6791 : p235 ∨ p423 ∨ (¬ p1154) ∨ (¬ p1155) ∨ (¬ p1156) ∨ (¬ p1157) ∨ (¬ p1158)) : p423 ∨ (¬ p1149) ∨ (¬ p1151) ∨ p235 ∨ (¬ p1152) ∨ (¬ p1153) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p1149 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1151 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p235) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1152 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1153 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1150) := by
    rcases h6766 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u1)
    · exact q3
    · exact False.elim (q4 u2)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u5)
  have u7 : p1154 := by
    rcases h6869 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1155 := by
    rcases h6870 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1156 := by
    rcases h6871 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1157 := by
    rcases h6872 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1158 := by
    rcases h6873 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h6791 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step24271 (p235 p423 p1149 p1151 p1152 p1153 : Prop)
    (h22196 : p1149 ∨ p235 ∨ p423)
    (h22197 : p1153 ∨ p235 ∨ p423)
    (h22198 : p1152 ∨ p235 ∨ p423)
    (h22199 : p1151 ∨ p235 ∨ p423)
    (h24270 : p423 ∨ (¬ p1149) ∨ (¬ p1151) ∨ p235 ∨ (¬ p1152) ∨ (¬ p1153)) : p423 ∨ p235 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p235) := fun hu => hn (Or.inr hu)
  have u2 : p1149 := by
    rcases h22196 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u3 : p1153 := by
    rcases h22197 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u4 : p1152 := by
    rcases h22198 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u5 : p1151 := by
    rcases h22199 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  rcases h24270 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step24272 (p18 p44 p50 p69 p134 p235 p422 p1145 p1207 p1229 p1256 : Prop)
    (h10749 : (¬ p69) ∨ (¬ p235) ∨ (¬ p1229))
    (h24269 : p1145 ∨ p235)
    (h11576 : (¬ p134) ∨ (¬ p1207) ∨ (¬ p1256))
    (h23796 : (¬ p44) ∨ p18 ∨ (¬ p134))
    (h21637 : p1256 ∨ p422)
    (h22877 : p50 ∨ p44)
    (h16735 : (¬ p50) ∨ (¬ p69) ∨ (¬ p422) ∨ (¬ p1145) ∨ (¬ p1229)) : (¬ p134) ∨ (¬ p1207) ∨ p18 ∨ (¬ p69) ∨ (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p235) := by
    rcases h10749 with q0 | q1 | q2
    · exact False.elim (q0 u3)
    · exact q1
    · exact False.elim (q2 u4)
  have u6 : p1145 := by
    rcases h24269 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u7 : (¬ p1256) := by
    rcases h11576 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact False.elim (q1 u1)
    · exact q2
  have u8 : (¬ p44) := by
    rcases h23796 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u0)
  have u9 : p422 := by
    rcases h21637 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p50 := by
    rcases h22877 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h16735 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u4)

theorem step24273 (p455 p456 p457 p461 p495 p636 p1078 p1084 p1229 : Prop)
    (h10248 : (¬ p457) ∨ (¬ p495) ∨ (¬ p1229))
    (h24029 : p457 ∨ p455)
    (h8768 : (¬ p455) ∨ (¬ p456))
    (h22380 : p461 ∨ p457)
    (h16594 : (¬ p461) ∨ (¬ p495) ∨ (¬ p636) ∨ (¬ p1084) ∨ (¬ p1229))
    (h14068 : p456 ∨ (¬ p636) ∨ (¬ p1078))
    (h21635 : p1084 ∨ p1078) : (¬ p636) ∨ (¬ p495) ∨ (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p457) := by
    rcases h10248 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u1)
    · exact False.elim (q2 u2)
  have u4 : p455 := by
    rcases h24029 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  have u5 : (¬ p456) := by
    rcases h8768 with q0 | q1
    · exact False.elim (q0 u4)
    · exact q1
  have u6 : p461 := by
    rcases h22380 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : (¬ p1084) := by
    rcases h16594 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u6)
    · exact False.elim (q1 u1)
    · exact False.elim (q2 u0)
    · exact q3
    · exact False.elim (q4 u2)
  have u8 : (¬ p1078) := by
    rcases h14068 with q0 | q1 | q2
    · exact False.elim (u5 q0)
    · exact False.elim (q1 u0)
    · exact q2
  rcases h21635 with q0 | q1
  · exact False.elim (u7 q0)
  · exact False.elim (u8 q1)

theorem step24274 (p124 p304 p425 p494 p580 p633 p1229 p1274 : Prop)
    (h21106 : p124 ∨ p304)
    (h11157 : p124 ∨ (¬ p425) ∨ (¬ p633))
    (h16762 : (¬ p304) ∨ (¬ p494) ∨ (¬ p580) ∨ (¬ p633) ∨ (¬ p1229) ∨ (¬ p1274))
    (h22344 : p425 ∨ p494) : p124 ∨ (¬ p1274) ∨ (¬ p580) ∨ (¬ p633) ∨ (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p1274 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p580 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p304 := by
    rcases h21106 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : (¬ p425) := by
    rcases h11157 with q0 | q1 | q2
    · exact False.elim (u0 q0)
    · exact q1
    · exact False.elim (q2 u3)
  have u7 : (¬ p494) := by
    rcases h16762 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u5)
    · exact q1
    · exact False.elim (q2 u2)
    · exact False.elim (q3 u3)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u1)
  rcases h22344 with q0 | q1
  · exact False.elim (u6 q0)
  · exact False.elim (u7 q1)

theorem step24275 (p425 p494 p495 p498 : Prop)
    (h12952 : p494 ∨ p498)
    (h22344 : p425 ∨ p494)
    (h8739 : (¬ p425) ∨ (¬ p495) ∨ (¬ p498)) : p494 ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p494) := fun hu => hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p498 := by
    rcases h12952 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p425 := by
    rcases h22344 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8739 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)

theorem step24277 (p17 p268 p269 p270 p271 p272 p273 p274 p275 p276 p277 p278 : Prop)
    (h1352 : p17 ∨ p268 ∨ (¬ p274) ∨ (¬ p275) ∨ (¬ p276) ∨ (¬ p277) ∨ (¬ p278))
    (h1414 : p269 ∨ p275)
    (h1419 : p270 ∨ p275)
    (h1424 : p271 ∨ p275)
    (h1429 : p272 ∨ p275)
    (h1434 : p273 ∨ p275)
    (h1327 : p17 ∨ p268 ∨ (¬ p269) ∨ (¬ p270) ∨ (¬ p271) ∨ (¬ p272) ∨ (¬ p273)) : (¬ p278) ∨ (¬ p276) ∨ p17 ∨ (¬ p277) ∨ (¬ p274) ∨ p268 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p278 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p276 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p277 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p274 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p268) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p275) := by
    rcases h1352 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u5 q1)
    · exact False.elim (q2 u4)
    · exact q3
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u3)
    · exact False.elim (q6 u0)
  have u7 : p269 := by
    rcases h1414 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p270 := by
    rcases h1419 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p271 := by
    rcases h1424 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p272 := by
    rcases h1429 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p273 := by
    rcases h1434 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h1327 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step24278 (p17 p268 p274 p276 p277 p278 : Prop)
    (h21695 : p276 ∨ p268 ∨ p17)
    (h21696 : p277 ∨ p268 ∨ p17)
    (h21697 : p278 ∨ p268 ∨ p17)
    (h21698 : p274 ∨ p268 ∨ p17)
    (h24277 : (¬ p278) ∨ (¬ p276) ∨ p17 ∨ (¬ p277) ∨ (¬ p274) ∨ p268) : p268 ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p268) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr hu)
  have u2 : p276 := by
    rcases h21695 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p277 := by
    rcases h21696 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p278 := by
    rcases h21697 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p274 := by
    rcases h21698 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h24277 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)
  · exact False.elim (u0 q5)

theorem step24279 (p1076 p1084 p1088 p1090 p1091 p1092 p1093 p1094 : Prop)
    (h6465 : p1088 ∨ p1090)
    (h6466 : p1088 ∨ p1091)
    (h6467 : p1088 ∨ p1092)
    (h6468 : p1088 ∨ p1093)
    (h6469 : p1088 ∨ p1094)
    (h6388 : p1076 ∨ p1084 ∨ (¬ p1090) ∨ (¬ p1091) ∨ (¬ p1092) ∨ (¬ p1093) ∨ (¬ p1094)) : p1088 ∨ p1084 ∨ p1076 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1088) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1084) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1090 := by
    rcases h6465 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1091 := by
    rcases h6466 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1092 := by
    rcases h6467 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1093 := by
    rcases h6468 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1094 := by
    rcases h6469 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6388 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24280 (p1076 p1084 p1085 p1086 p1087 p1088 p1089 p1093 : Prop)
    (h24279 : p1088 ∨ p1084 ∨ p1076)
    (h6453 : p1085 ∨ p1093)
    (h6458 : p1086 ∨ p1093)
    (h6463 : p1087 ∨ p1093)
    (h6473 : p1089 ∨ p1093)
    (h6363 : p1076 ∨ p1084 ∨ (¬ p1085) ∨ (¬ p1086) ∨ (¬ p1087) ∨ (¬ p1088) ∨ (¬ p1089)) : p1093 ∨ p1084 ∨ p1076 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1093) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1084) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1088 := by
    rcases h24279 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1085 := by
    rcases h6453 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1086 := by
    rcases h6458 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1087 := by
    rcases h6463 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1089 := by
    rcases h6473 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6363 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24281 (p1076 p1084 p1085 p1086 p1087 p1088 p1089 p1092 : Prop)
    (h24279 : p1088 ∨ p1084 ∨ p1076)
    (h6452 : p1085 ∨ p1092)
    (h6457 : p1086 ∨ p1092)
    (h6462 : p1087 ∨ p1092)
    (h6472 : p1089 ∨ p1092)
    (h6363 : p1076 ∨ p1084 ∨ (¬ p1085) ∨ (¬ p1086) ∨ (¬ p1087) ∨ (¬ p1088) ∨ (¬ p1089)) : p1092 ∨ p1084 ∨ p1076 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1092) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1084) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1088 := by
    rcases h24279 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1085 := by
    rcases h6452 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1086 := by
    rcases h6457 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1087 := by
    rcases h6462 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1089 := by
    rcases h6472 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6363 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24282 (p1076 p1084 p1085 p1086 p1087 p1088 p1089 p1094 : Prop)
    (h24279 : p1088 ∨ p1084 ∨ p1076)
    (h6454 : p1085 ∨ p1094)
    (h6459 : p1086 ∨ p1094)
    (h6464 : p1087 ∨ p1094)
    (h6474 : p1089 ∨ p1094)
    (h6363 : p1076 ∨ p1084 ∨ (¬ p1085) ∨ (¬ p1086) ∨ (¬ p1087) ∨ (¬ p1088) ∨ (¬ p1089)) : p1094 ∨ p1084 ∨ p1076 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1094) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1084) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1088 := by
    rcases h24279 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1085 := by
    rcases h6454 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1086 := by
    rcases h6459 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1087 := by
    rcases h6464 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1089 := by
    rcases h6474 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6363 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24283 (p1076 p1084 p1085 p1086 p1087 p1088 p1089 p1090 : Prop)
    (h24279 : p1088 ∨ p1084 ∨ p1076)
    (h6450 : p1085 ∨ p1090)
    (h6455 : p1086 ∨ p1090)
    (h6460 : p1087 ∨ p1090)
    (h6470 : p1089 ∨ p1090)
    (h6363 : p1076 ∨ p1084 ∨ (¬ p1085) ∨ (¬ p1086) ∨ (¬ p1087) ∨ (¬ p1088) ∨ (¬ p1089)) : p1090 ∨ p1084 ∨ p1076 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1090) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1084) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1088 := by
    rcases h24279 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1085 := by
    rcases h6450 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1086 := by
    rcases h6455 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1087 := by
    rcases h6460 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1089 := by
    rcases h6470 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6363 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24284 (p1076 p1084 p1085 p1086 p1087 p1088 p1089 p1090 p1091 p1092 p1093 p1094 : Prop)
    (h24279 : p1088 ∨ p1084 ∨ p1076)
    (h24280 : p1093 ∨ p1084 ∨ p1076)
    (h24281 : p1092 ∨ p1084 ∨ p1076)
    (h24282 : p1094 ∨ p1084 ∨ p1076)
    (h24283 : p1090 ∨ p1084 ∨ p1076)
    (h6388 : p1076 ∨ p1084 ∨ (¬ p1090) ∨ (¬ p1091) ∨ (¬ p1092) ∨ (¬ p1093) ∨ (¬ p1094))
    (h6451 : p1085 ∨ p1091)
    (h6456 : p1086 ∨ p1091)
    (h6461 : p1087 ∨ p1091)
    (h6471 : p1089 ∨ p1091)
    (h6363 : p1076 ∨ p1084 ∨ (¬ p1085) ∨ (¬ p1086) ∨ (¬ p1087) ∨ (¬ p1088) ∨ (¬ p1089)) : p1084 ∨ p1076 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1084) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr hu)
  have u2 : p1088 := by
    rcases h24279 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1093 := by
    rcases h24280 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1092 := by
    rcases h24281 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1094 := by
    rcases h24282 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p1090 := by
    rcases h24283 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p1091) := by
    rcases h6388 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u6)
    · exact q3
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u3)
    · exact False.elim (q6 u5)
  have u8 : p1085 := by
    rcases h6451 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p1086 := by
    rcases h6456 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p1087 := by
    rcases h6461 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p1089 := by
    rcases h6471 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h6363 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u11)

theorem step24285 (p137 p143 p144 p145 p146 p147 p148 p149 : Prop)
    (h756 : p144 ∨ p149)
    (h761 : p145 ∨ p149)
    (h766 : p146 ∨ p149)
    (h771 : p147 ∨ p149)
    (h776 : p148 ∨ p149)
    (h665 : p137 ∨ p143 ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p147) ∨ (¬ p148)) : p149 ∨ p143 ∨ p137 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p149) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p143) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p137) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p144 := by
    rcases h756 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p145 := by
    rcases h761 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p146 := by
    rcases h766 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p147 := by
    rcases h771 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p148 := by
    rcases h776 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h665 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24286 (p137 p143 p144 p145 p146 p147 p148 p150 : Prop)
    (h757 : p144 ∨ p150)
    (h762 : p145 ∨ p150)
    (h767 : p146 ∨ p150)
    (h772 : p147 ∨ p150)
    (h777 : p148 ∨ p150)
    (h665 : p137 ∨ p143 ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p147) ∨ (¬ p148)) : p150 ∨ p143 ∨ p137 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p150) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p143) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p137) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p144 := by
    rcases h757 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p145 := by
    rcases h762 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p146 := by
    rcases h767 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p147 := by
    rcases h772 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p148 := by
    rcases h777 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h665 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24287 (p137 p143 p144 p145 p146 p147 p148 p151 : Prop)
    (h758 : p144 ∨ p151)
    (h763 : p145 ∨ p151)
    (h768 : p146 ∨ p151)
    (h773 : p147 ∨ p151)
    (h778 : p148 ∨ p151)
    (h665 : p137 ∨ p143 ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p147) ∨ (¬ p148)) : p151 ∨ p143 ∨ p137 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p151) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p143) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p137) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p144 := by
    rcases h758 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p145 := by
    rcases h763 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p146 := by
    rcases h768 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p147 := by
    rcases h773 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p148 := by
    rcases h778 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h665 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24288 (p137 p143 p144 p145 p146 p147 p148 p152 : Prop)
    (h759 : p144 ∨ p152)
    (h764 : p145 ∨ p152)
    (h769 : p146 ∨ p152)
    (h774 : p147 ∨ p152)
    (h779 : p148 ∨ p152)
    (h665 : p137 ∨ p143 ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p147) ∨ (¬ p148)) : p152 ∨ p143 ∨ p137 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p152) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p143) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p137) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p144 := by
    rcases h759 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p145 := by
    rcases h764 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p146 := by
    rcases h769 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p147 := by
    rcases h774 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p148 := by
    rcases h779 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h665 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24289 (p134 p137 p143 p144 p145 p146 p147 p148 p149 p150 p151 p152 p153 : Prop)
    (h24285 : p149 ∨ p143 ∨ p137)
    (h24286 : p150 ∨ p143 ∨ p137)
    (h24287 : p151 ∨ p143 ∨ p137)
    (h24288 : p152 ∨ p143 ∨ p137)
    (h695 : p134 ∨ p143 ∨ (¬ p149) ∨ (¬ p150) ∨ (¬ p151) ∨ (¬ p152) ∨ (¬ p153))
    (h760 : p144 ∨ p153)
    (h765 : p145 ∨ p153)
    (h770 : p146 ∨ p153)
    (h775 : p147 ∨ p153)
    (h780 : p148 ∨ p153)
    (h665 : p137 ∨ p143 ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p147) ∨ (¬ p148)) : p143 ∨ p134 ∨ p137 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p143) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p134) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p137) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p149 := by
    rcases h24285 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u4 : p150 := by
    rcases h24286 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u5 : p151 := by
    rcases h24287 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u6 : p152 := by
    rcases h24288 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u7 : (¬ p153) := by
    rcases h695 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p144 := by
    rcases h760 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p145 := by
    rcases h765 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p146 := by
    rcases h770 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p147 := by
    rcases h775 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u12 : p148 := by
    rcases h780 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h665 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u12)

theorem step24290 (p18 p27 p28 p29 p30 p31 p32 p37 : Prop)
    (h109 : p28 ∨ p37)
    (h114 : p29 ∨ p37)
    (h119 : p30 ∨ p37)
    (h124 : p31 ∨ p37)
    (h129 : p32 ∨ p37)
    (h19 : p18 ∨ p27 ∨ (¬ p28) ∨ (¬ p29) ∨ (¬ p30) ∨ (¬ p31) ∨ (¬ p32)) : p37 ∨ p27 ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p37) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p27) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p28 := by
    rcases h109 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p29 := by
    rcases h114 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p30 := by
    rcases h119 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p31 := by
    rcases h124 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p32 := by
    rcases h129 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24291 (p18 p27 p28 p33 p34 p35 p36 p37 : Prop)
    (h24290 : p37 ∨ p27 ∨ p18)
    (h105 : p28 ∨ p33)
    (h106 : p28 ∨ p34)
    (h107 : p28 ∨ p35)
    (h108 : p28 ∨ p36)
    (h44 : p18 ∨ p27 ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p36) ∨ (¬ p37)) : p28 ∨ p27 ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p28) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p27) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p37 := by
    rcases h24290 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p33 := by
    rcases h105 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p34 := by
    rcases h106 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p35 := by
    rcases h107 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p36 := by
    rcases h108 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h44 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step24292 (p18 p27 p29 p33 p34 p35 p36 p37 : Prop)
    (h24290 : p37 ∨ p27 ∨ p18)
    (h110 : p29 ∨ p33)
    (h111 : p29 ∨ p34)
    (h112 : p29 ∨ p35)
    (h113 : p29 ∨ p36)
    (h44 : p18 ∨ p27 ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p36) ∨ (¬ p37)) : p29 ∨ p27 ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p29) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p27) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p37 := by
    rcases h24290 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p33 := by
    rcases h110 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p34 := by
    rcases h111 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p35 := by
    rcases h112 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p36 := by
    rcases h113 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h44 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step24293 (p18 p27 p30 p33 p34 p35 p36 p37 : Prop)
    (h24290 : p37 ∨ p27 ∨ p18)
    (h115 : p30 ∨ p33)
    (h116 : p30 ∨ p34)
    (h117 : p30 ∨ p35)
    (h118 : p30 ∨ p36)
    (h44 : p18 ∨ p27 ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p36) ∨ (¬ p37)) : p30 ∨ p27 ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p30) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p27) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p37 := by
    rcases h24290 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p33 := by
    rcases h115 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p34 := by
    rcases h116 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p35 := by
    rcases h117 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p36 := by
    rcases h118 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h44 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step24294 (p18 p27 p31 p33 p34 p35 p36 p37 : Prop)
    (h24290 : p37 ∨ p27 ∨ p18)
    (h120 : p31 ∨ p33)
    (h121 : p31 ∨ p34)
    (h122 : p31 ∨ p35)
    (h123 : p31 ∨ p36)
    (h44 : p18 ∨ p27 ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p36) ∨ (¬ p37)) : p31 ∨ p27 ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p31) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p27) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p37 := by
    rcases h24290 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p33 := by
    rcases h120 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p34 := by
    rcases h121 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p35 := by
    rcases h122 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p36 := by
    rcases h123 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h44 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step24295 (p18 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 : Prop)
    (h24290 : p37 ∨ p27 ∨ p18)
    (h24291 : p28 ∨ p27 ∨ p18)
    (h24292 : p29 ∨ p27 ∨ p18)
    (h24293 : p30 ∨ p27 ∨ p18)
    (h24294 : p31 ∨ p27 ∨ p18)
    (h19 : p18 ∨ p27 ∨ (¬ p28) ∨ (¬ p29) ∨ (¬ p30) ∨ (¬ p31) ∨ (¬ p32))
    (h125 : p32 ∨ p33)
    (h126 : p32 ∨ p34)
    (h127 : p32 ∨ p35)
    (h128 : p32 ∨ p36)
    (h44 : p18 ∨ p27 ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p36) ∨ (¬ p37)) : p27 ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p27) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p18) := fun hu => hn (Or.inr hu)
  have u2 : p37 := by
    rcases h24290 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p28 := by
    rcases h24291 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p29 := by
    rcases h24292 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p30 := by
    rcases h24293 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p31 := by
    rcases h24294 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p32) := by
    rcases h19 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p33 := by
    rcases h125 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p34 := by
    rcases h126 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p35 := by
    rcases h127 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p36 := by
    rcases h128 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h44 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u2)

theorem step24296 (p636 p640 p646 p648 p649 p650 p651 p652 : Prop)
    (h3731 : p646 ∨ p648)
    (h3732 : p646 ∨ p649)
    (h3733 : p646 ∨ p650)
    (h3734 : p646 ∨ p651)
    (h3735 : p646 ∨ p652)
    (h3652 : p636 ∨ p640 ∨ (¬ p648) ∨ (¬ p649) ∨ (¬ p650) ∨ (¬ p651) ∨ (¬ p652)) : p646 ∨ p640 ∨ p636 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p646) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p640) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p636) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p648 := by
    rcases h3731 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p649 := by
    rcases h3732 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p650 := by
    rcases h3733 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p651 := by
    rcases h3734 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p652 := by
    rcases h3735 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3652 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24297 (p636 p640 p643 p644 p645 p646 p647 p652 : Prop)
    (h24296 : p646 ∨ p640 ∨ p636)
    (h3720 : p643 ∨ p652)
    (h3725 : p644 ∨ p652)
    (h3730 : p645 ∨ p652)
    (h3740 : p647 ∨ p652)
    (h3627 : p636 ∨ p640 ∨ (¬ p643) ∨ (¬ p644) ∨ (¬ p645) ∨ (¬ p646) ∨ (¬ p647)) : p652 ∨ p640 ∨ p636 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p652) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p640) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p636) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p646 := by
    rcases h24296 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p643 := by
    rcases h3720 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p644 := by
    rcases h3725 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p645 := by
    rcases h3730 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p647 := by
    rcases h3740 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3627 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24298 (p636 p640 p643 p644 p645 p646 p647 p648 : Prop)
    (h24296 : p646 ∨ p640 ∨ p636)
    (h3716 : p643 ∨ p648)
    (h3721 : p644 ∨ p648)
    (h3726 : p645 ∨ p648)
    (h3736 : p647 ∨ p648)
    (h3627 : p636 ∨ p640 ∨ (¬ p643) ∨ (¬ p644) ∨ (¬ p645) ∨ (¬ p646) ∨ (¬ p647)) : p648 ∨ p640 ∨ p636 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p648) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p640) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p636) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p646 := by
    rcases h24296 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p643 := by
    rcases h3716 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p644 := by
    rcases h3721 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p645 := by
    rcases h3726 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p647 := by
    rcases h3736 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3627 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24299 (p636 p640 p643 p644 p645 p646 p647 p649 : Prop)
    (h24296 : p646 ∨ p640 ∨ p636)
    (h3717 : p643 ∨ p649)
    (h3722 : p644 ∨ p649)
    (h3727 : p645 ∨ p649)
    (h3737 : p647 ∨ p649)
    (h3627 : p636 ∨ p640 ∨ (¬ p643) ∨ (¬ p644) ∨ (¬ p645) ∨ (¬ p646) ∨ (¬ p647)) : p649 ∨ p640 ∨ p636 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p649) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p640) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p636) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p646 := by
    rcases h24296 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p643 := by
    rcases h3717 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p644 := by
    rcases h3722 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p645 := by
    rcases h3727 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p647 := by
    rcases h3737 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3627 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24300 (p636 p640 p643 p644 p645 p646 p647 p650 : Prop)
    (h24296 : p646 ∨ p640 ∨ p636)
    (h3718 : p643 ∨ p650)
    (h3723 : p644 ∨ p650)
    (h3728 : p645 ∨ p650)
    (h3738 : p647 ∨ p650)
    (h3627 : p636 ∨ p640 ∨ (¬ p643) ∨ (¬ p644) ∨ (¬ p645) ∨ (¬ p646) ∨ (¬ p647)) : p650 ∨ p640 ∨ p636 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p650) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p640) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p636) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p646 := by
    rcases h24296 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p643 := by
    rcases h3718 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p644 := by
    rcases h3723 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p645 := by
    rcases h3728 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p647 := by
    rcases h3738 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3627 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24301 (p636 p640 p643 p644 p645 p646 p647 p648 p649 p650 p651 p652 : Prop)
    (h24296 : p646 ∨ p640 ∨ p636)
    (h24297 : p652 ∨ p640 ∨ p636)
    (h24298 : p648 ∨ p640 ∨ p636)
    (h24299 : p649 ∨ p640 ∨ p636)
    (h24300 : p650 ∨ p640 ∨ p636)
    (h3652 : p636 ∨ p640 ∨ (¬ p648) ∨ (¬ p649) ∨ (¬ p650) ∨ (¬ p651) ∨ (¬ p652))
    (h3719 : p643 ∨ p651)
    (h3724 : p644 ∨ p651)
    (h3729 : p645 ∨ p651)
    (h3739 : p647 ∨ p651)
    (h3627 : p636 ∨ p640 ∨ (¬ p643) ∨ (¬ p644) ∨ (¬ p645) ∨ (¬ p646) ∨ (¬ p647)) : p640 ∨ p636 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p640) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p636) := fun hu => hn (Or.inr hu)
  have u2 : p646 := by
    rcases h24296 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p652 := by
    rcases h24297 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p648 := by
    rcases h24298 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p649 := by
    rcases h24299 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p650 := by
    rcases h24300 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p651) := by
    rcases h3652 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u6)
    · exact q5
    · exact False.elim (q6 u3)
  have u8 : p643 := by
    rcases h3719 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p644 := by
    rcases h3724 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p645 := by
    rcases h3729 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p647 := by
    rcases h3739 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h3627 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u11)

theorem step24302 (p137 p142 p144 p145 p146 p147 p148 p153 : Prop)
    (h22145 : p148 ∨ p137 ∨ p142)
    (h760 : p144 ∨ p153)
    (h765 : p145 ∨ p153)
    (h770 : p146 ∨ p153)
    (h775 : p147 ∨ p153)
    (h663 : p137 ∨ p142 ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p147) ∨ (¬ p148)) : p153 ∨ p142 ∨ p137 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p153) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p142) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p137) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p148 := by
    rcases h22145 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u2 q1)
    · exact False.elim (u1 q2)
  have u4 : p144 := by
    rcases h760 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p145 := by
    rcases h765 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p146 := by
    rcases h770 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p147 := by
    rcases h775 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h663 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step24303 (p137 p142 p144 p149 p150 p151 p152 p153 : Prop)
    (h24302 : p153 ∨ p142 ∨ p137)
    (h756 : p144 ∨ p149)
    (h757 : p144 ∨ p150)
    (h758 : p144 ∨ p151)
    (h759 : p144 ∨ p152)
    (h688 : p137 ∨ p142 ∨ (¬ p149) ∨ (¬ p150) ∨ (¬ p151) ∨ (¬ p152) ∨ (¬ p153)) : p144 ∨ p142 ∨ p137 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p144) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p142) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p137) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p153 := by
    rcases h24302 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p149 := by
    rcases h756 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p150 := by
    rcases h757 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p151 := by
    rcases h758 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p152 := by
    rcases h759 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h688 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step24304 (p137 p142 p145 p149 p150 p151 p152 p153 : Prop)
    (h24302 : p153 ∨ p142 ∨ p137)
    (h761 : p145 ∨ p149)
    (h762 : p145 ∨ p150)
    (h763 : p145 ∨ p151)
    (h764 : p145 ∨ p152)
    (h688 : p137 ∨ p142 ∨ (¬ p149) ∨ (¬ p150) ∨ (¬ p151) ∨ (¬ p152) ∨ (¬ p153)) : p145 ∨ p142 ∨ p137 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p145) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p142) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p137) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p153 := by
    rcases h24302 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p149 := by
    rcases h761 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p150 := by
    rcases h762 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p151 := by
    rcases h763 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p152 := by
    rcases h764 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h688 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step24305 (p137 p142 p146 p149 p150 p151 p152 p153 : Prop)
    (h24302 : p153 ∨ p142 ∨ p137)
    (h766 : p146 ∨ p149)
    (h767 : p146 ∨ p150)
    (h768 : p146 ∨ p151)
    (h769 : p146 ∨ p152)
    (h688 : p137 ∨ p142 ∨ (¬ p149) ∨ (¬ p150) ∨ (¬ p151) ∨ (¬ p152) ∨ (¬ p153)) : p146 ∨ p142 ∨ p137 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p146) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p142) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p137) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p153 := by
    rcases h24302 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p149 := by
    rcases h766 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p150 := by
    rcases h767 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p151 := by
    rcases h768 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p152 := by
    rcases h769 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h688 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step24306 (p137 p142 p144 p145 p146 p147 p148 p149 p150 p151 p152 p153 : Prop)
    (h22145 : p148 ∨ p137 ∨ p142)
    (h24302 : p153 ∨ p142 ∨ p137)
    (h24303 : p144 ∨ p142 ∨ p137)
    (h24304 : p145 ∨ p142 ∨ p137)
    (h24305 : p146 ∨ p142 ∨ p137)
    (h663 : p137 ∨ p142 ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p147) ∨ (¬ p148))
    (h771 : p147 ∨ p149)
    (h772 : p147 ∨ p150)
    (h773 : p147 ∨ p151)
    (h774 : p147 ∨ p152)
    (h688 : p137 ∨ p142 ∨ (¬ p149) ∨ (¬ p150) ∨ (¬ p151) ∨ (¬ p152) ∨ (¬ p153)) : p142 ∨ p137 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p142) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p137) := fun hu => hn (Or.inr hu)
  have u2 : p148 := by
    rcases h22145 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u3 : p153 := by
    rcases h24302 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p144 := by
    rcases h24303 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p145 := by
    rcases h24304 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p146 := by
    rcases h24305 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p147) := by
    rcases h663 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u6)
    · exact q5
    · exact False.elim (q6 u2)
  have u8 : p149 := by
    rcases h771 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p150 := by
    rcases h772 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p151 := by
    rcases h773 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p152 := by
    rcases h774 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h688 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u3)

theorem step24307 (p18 p27 p47 p101 p102 p142 p193 p346 p640 p904 p1077 : Prop)
    (h17269 : (¬ p102) ∨ (¬ p142) ∨ (¬ p193) ∨ (¬ p1077))
    (h13198 : (¬ p18) ∨ (¬ p47) ∨ (¬ p142))
    (h21623 : p101 ∨ p102)
    (h24295 : p27 ∨ p18)
    (h17404 : (¬ p27) ∨ (¬ p101) ∨ (¬ p346) ∨ (¬ p640) ∨ (¬ p904)) : (¬ p142) ∨ (¬ p640) ∨ (¬ p47) ∨ (¬ p193) ∨ (¬ p346) ∨ (¬ p904) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p640 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p102) := by
    rcases h17269 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u6)
  have u8 : (¬ p18) := by
    rcases h13198 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u0)
  have u9 : p101 := by
    rcases h21623 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p27 := by
    rcases h24295 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h17404 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)

theorem step24308 (p186 p187 p189 p196 p197 p198 p199 p200 p201 p202 p203 p204 p205 : Prop)
    (h21252 : p201 ∨ p186 ∨ p189)
    (h21253 : p202 ∨ p186 ∨ p189)
    (h21254 : p203 ∨ p186 ∨ p189)
    (h21255 : p204 ∨ p186 ∨ p189)
    (h958 : p186 ∨ p189 ∨ (¬ p201) ∨ (¬ p202) ∨ (¬ p203) ∨ (¬ p204) ∨ (¬ p205))
    (h1026 : p196 ∨ p205)
    (h1031 : p197 ∨ p205)
    (h1036 : p198 ∨ p205)
    (h1041 : p199 ∨ p205)
    (h1046 : p200 ∨ p205)
    (h928 : p186 ∨ p187 ∨ (¬ p196) ∨ (¬ p197) ∨ (¬ p198) ∨ (¬ p199) ∨ (¬ p200)) : p186 ∨ p187 ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p186) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p187) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p201 := by
    rcases h21252 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u4 : p202 := by
    rcases h21253 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u5 : p203 := by
    rcases h21254 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u6 : p204 := by
    rcases h21255 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u7 : (¬ p205) := by
    rcases h958 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u0 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p196 := by
    rcases h1026 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p197 := by
    rcases h1031 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p198 := by
    rcases h1036 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p199 := by
    rcases h1041 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u12 : p200 := by
    rcases h1046 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h928 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u12)

theorem step24309 (p12 p101 p103 p107 p127 p134 p142 p163 p186 p1077 : Prop)
    (h22176 : p142 ∨ p134)
    (h13830 : (¬ p103) ∨ p142 ∨ (¬ p163))
    (h16759 : (¬ p12) ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p163) ∨ (¬ p186))
    (h21287 : p107 ∨ p103 ∨ p101)
    (h13032 : p12 ∨ (¬ p107) ∨ (¬ p1077)) : (¬ p163) ∨ (¬ p186) ∨ (¬ p127) ∨ p101 ∨ p142 ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p142) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p134 := by
    rcases h22176 with q0 | q1
    · exact False.elim (u4 q0)
    · exact q1
  have u7 : (¬ p103) := by
    rcases h13830 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u4 q1)
    · exact False.elim (q2 u0)
  have u8 : (¬ p12) := by
    rcases h16759 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u6)
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u1)
  have u9 : p107 := by
    rcases h21287 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u7 q1)
    · exact False.elim (u3 q2)
  rcases h13032 with q0 | q1 | q2
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u5)

theorem step24310 (p6 p14 p15 p18 p19 p44 p48 p50 p64 p69 p101 p102 p108 p127 p134 p142 p163 p167 p186 p187 p189 p225 p346 p422 p544 p668 p1036 p1041 p1077 p1141 p1145 p1212 p1229 p1256 p1274 : Prop)
    (h22658 : p108 ∨ p101)
    (h21623 : p101 ∨ p102)
    (h22176 : p142 ∨ p134)
    (h22840 : p19 ∨ p18)
    (h23796 : (¬ p44) ∨ p18 ∨ (¬ p134))
    (h17440 : (¬ p15) ∨ (¬ p19) ∨ (¬ p102) ∨ (¬ p1077))
    (h11355 : (¬ p19) ∨ (¬ p1141) ∨ (¬ p1212))
    (h14142 : p14 ∨ (¬ p19) ∨ (¬ p108))
    (h21322 : p48 ∨ p44)
    (h22877 : p50 ∨ p44)
    (h21316 : p64 ∨ p15)
    (h21946 : p69 ∨ p15)
    (h21560 : p1145 ∨ p1141)
    (h17991 : (¬ p14) ∨ (¬ p346) ∨ (¬ p544) ∨ (¬ p1077))
    (h16761 : (¬ p6) ∨ (¬ p19) ∨ (¬ p48) ∨ (¬ p64) ∨ (¬ p1229) ∨ (¬ p1274))
    (h16735 : (¬ p50) ∨ (¬ p69) ∨ (¬ p422) ∨ (¬ p1145) ∨ (¬ p1229))
    (h22947 : p544 ∨ p225)
    (h22605 : p127 ∨ p6)
    (h11670 : p6 ∨ (¬ p134) ∨ (¬ p187))
    (h21637 : p1256 ∨ p422)
    (h24308 : p186 ∨ p187 ∨ p189)
    (h24309 : (¬ p163) ∨ (¬ p186) ∨ (¬ p127) ∨ p101 ∨ p142 ∨ (¬ p1077))
    (h21282 : p163 ∨ p167)
    (h20412 : (¬ p167) ∨ (¬ p346) ∨ (¬ p1036) ∨ (¬ p1077))
    (h16821 : (¬ p167) ∨ (¬ p225) ∨ (¬ p668) ∨ (¬ p1041) ∨ (¬ p1256))
    (h20717 : p1036 ∨ p1041) : p18 ∨ (¬ p1212) ∨ p101 ∨ p142 ∨ (¬ p1274) ∨ p189 ∨ (¬ p346) ∨ (¬ p668) ∨ (¬ p1077) ∨ (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p18) := fun hu => hn (Or.inl hu)
  have u1 : p1212 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p142) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1274 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p108 := by
    rcases h22658 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : p102 := by
    rcases h21623 with q0 | q1
    · exact False.elim (u2 q0)
    · exact q1
  have u12 : p134 := by
    rcases h22176 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  have u13 : p19 := by
    rcases h22840 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u14 : (¬ p44) := by
    rcases h23796 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u12)
  have u15 : (¬ p15) := by
    rcases h17440 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u13)
    · exact False.elim (q2 u11)
    · exact False.elim (q3 u8)
  have u16 : (¬ p1141) := by
    rcases h11355 with q0 | q1 | q2
    · exact False.elim (q0 u13)
    · exact q1
    · exact False.elim (q2 u1)
  have u17 : p14 := by
    rcases h14142 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u13)
    · exact False.elim (q2 u10)
  have u18 : p48 := by
    rcases h21322 with q0 | q1
    · exact q0
    · exact False.elim (u14 q1)
  have u19 : p50 := by
    rcases h22877 with q0 | q1
    · exact q0
    · exact False.elim (u14 q1)
  have u20 : p64 := by
    rcases h21316 with q0 | q1
    · exact q0
    · exact False.elim (u15 q1)
  have u21 : p69 := by
    rcases h21946 with q0 | q1
    · exact q0
    · exact False.elim (u15 q1)
  have u22 : p1145 := by
    rcases h21560 with q0 | q1
    · exact q0
    · exact False.elim (u16 q1)
  have u23 : (¬ p544) := by
    rcases h17991 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u17)
    · exact False.elim (q1 u6)
    · exact q2
    · exact False.elim (q3 u8)
  have u24 : (¬ p6) := by
    rcases h16761 with q0 | q1 | q2 | q3 | q4 | q5
    · exact q0
    · exact False.elim (q1 u13)
    · exact False.elim (q2 u18)
    · exact False.elim (q3 u20)
    · exact False.elim (q4 u9)
    · exact False.elim (q5 u4)
  have u25 : (¬ p422) := by
    rcases h16735 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u19)
    · exact False.elim (q1 u21)
    · exact q2
    · exact False.elim (q3 u22)
    · exact False.elim (q4 u9)
  have u26 : p225 := by
    rcases h22947 with q0 | q1
    · exact False.elim (u23 q0)
    · exact q1
  have u27 : p127 := by
    rcases h22605 with q0 | q1
    · exact q0
    · exact False.elim (u24 q1)
  have u28 : (¬ p187) := by
    rcases h11670 with q0 | q1 | q2
    · exact False.elim (u24 q0)
    · exact False.elim (q1 u12)
    · exact q2
  have u29 : p1256 := by
    rcases h21637 with q0 | q1
    · exact q0
    · exact False.elim (u25 q1)
  have u30 : p186 := by
    rcases h24308 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u28 q1)
    · exact False.elim (u5 q2)
  have u31 : (¬ p163) := by
    rcases h24309 with q0 | q1 | q2 | q3 | q4 | q5
    · exact q0
    · exact False.elim (q1 u30)
    · exact False.elim (q2 u27)
    · exact False.elim (u2 q3)
    · exact False.elim (u3 q4)
    · exact False.elim (q5 u8)
  have u32 : p167 := by
    rcases h21282 with q0 | q1
    · exact False.elim (u31 q0)
    · exact q1
  have u33 : (¬ p1036) := by
    rcases h20412 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u32)
    · exact False.elim (q1 u6)
    · exact q2
    · exact False.elim (q3 u8)
  have u34 : (¬ p1041) := by
    rcases h16821 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u32)
    · exact False.elim (q1 u26)
    · exact False.elim (q2 u7)
    · exact q3
    · exact False.elim (q4 u29)
  rcases h20717 with q0 | q1
  · exact False.elim (u33 q0)
  · exact False.elim (u34 q1)

theorem step24312 (p18 p69 p235 p1145 p1213 p1229 : Prop)
    (h10749 : (¬ p69) ∨ (¬ p235) ∨ (¬ p1229))
    (h16823 : (¬ p18) ∨ (¬ p69) ∨ (¬ p1145) ∨ (¬ p1213) ∨ (¬ p1229))
    (h24269 : p1145 ∨ p235) : (¬ p69) ∨ (¬ p18) ∨ (¬ p1213) ∨ (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
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
  have u4 : (¬ p235) := by
    rcases h10749 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (q2 u3)
  have u5 : (¬ p1145) := by
    rcases h16823 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u1)
    · exact False.elim (q1 u0)
    · exact q2
    · exact False.elim (q3 u2)
    · exact False.elim (q4 u3)
  rcases h24269 with q0 | q1
  · exact False.elim (u5 q0)
  · exact False.elim (u4 q1)

theorem step24313 (p69 p71 p73 p74 p75 p76 p77 p78 : Prop)
    (h369 : p73 ∨ p78)
    (h374 : p74 ∨ p78)
    (h379 : p75 ∨ p78)
    (h384 : p76 ∨ p78)
    (h389 : p77 ∨ p78)
    (h280 : p69 ∨ p71 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77)) : p78 ∨ p71 ∨ p69 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p78) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p71) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p69) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p73 := by
    rcases h369 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p74 := by
    rcases h374 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p75 := by
    rcases h379 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p76 := by
    rcases h384 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p77 := by
    rcases h389 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h280 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24314 (p69 p71 p73 p78 p79 p80 p81 p82 : Prop)
    (h24313 : p78 ∨ p71 ∨ p69)
    (h370 : p73 ∨ p79)
    (h371 : p73 ∨ p80)
    (h372 : p73 ∨ p81)
    (h373 : p73 ∨ p82)
    (h305 : p69 ∨ p71 ∨ (¬ p78) ∨ (¬ p79) ∨ (¬ p80) ∨ (¬ p81) ∨ (¬ p82)) : p73 ∨ p71 ∨ p69 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p73) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p71) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p69) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p78 := by
    rcases h24313 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p79 := by
    rcases h370 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p80 := by
    rcases h371 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p81 := by
    rcases h372 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p82 := by
    rcases h373 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h305 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24315 (p69 p71 p74 p78 p79 p80 p81 p82 : Prop)
    (h24313 : p78 ∨ p71 ∨ p69)
    (h375 : p74 ∨ p79)
    (h376 : p74 ∨ p80)
    (h377 : p74 ∨ p81)
    (h378 : p74 ∨ p82)
    (h305 : p69 ∨ p71 ∨ (¬ p78) ∨ (¬ p79) ∨ (¬ p80) ∨ (¬ p81) ∨ (¬ p82)) : p74 ∨ p71 ∨ p69 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p74) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p71) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p69) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p78 := by
    rcases h24313 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p79 := by
    rcases h375 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p80 := by
    rcases h376 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p81 := by
    rcases h377 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p82 := by
    rcases h378 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h305 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24316 (p69 p71 p75 p78 p79 p80 p81 p82 : Prop)
    (h24313 : p78 ∨ p71 ∨ p69)
    (h380 : p75 ∨ p79)
    (h381 : p75 ∨ p80)
    (h382 : p75 ∨ p81)
    (h383 : p75 ∨ p82)
    (h305 : p69 ∨ p71 ∨ (¬ p78) ∨ (¬ p79) ∨ (¬ p80) ∨ (¬ p81) ∨ (¬ p82)) : p75 ∨ p71 ∨ p69 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p75) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p71) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p69) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p78 := by
    rcases h24313 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p79 := by
    rcases h380 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p80 := by
    rcases h381 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p81 := by
    rcases h382 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p82 := by
    rcases h383 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h305 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24317 (p69 p71 p76 p78 p79 p80 p81 p82 : Prop)
    (h24313 : p78 ∨ p71 ∨ p69)
    (h385 : p76 ∨ p79)
    (h386 : p76 ∨ p80)
    (h387 : p76 ∨ p81)
    (h388 : p76 ∨ p82)
    (h305 : p69 ∨ p71 ∨ (¬ p78) ∨ (¬ p79) ∨ (¬ p80) ∨ (¬ p81) ∨ (¬ p82)) : p76 ∨ p71 ∨ p69 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p76) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p71) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p69) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p78 := by
    rcases h24313 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p79 := by
    rcases h385 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p80 := by
    rcases h386 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p81 := by
    rcases h387 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p82 := by
    rcases h388 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h305 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24318 (p69 p71 p73 p74 p75 p76 p77 p78 p79 p80 p81 p82 : Prop)
    (h24313 : p78 ∨ p71 ∨ p69)
    (h24314 : p73 ∨ p71 ∨ p69)
    (h24315 : p74 ∨ p71 ∨ p69)
    (h24316 : p75 ∨ p71 ∨ p69)
    (h24317 : p76 ∨ p71 ∨ p69)
    (h280 : p69 ∨ p71 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77))
    (h390 : p77 ∨ p79)
    (h391 : p77 ∨ p80)
    (h392 : p77 ∨ p81)
    (h393 : p77 ∨ p82)
    (h305 : p69 ∨ p71 ∨ (¬ p78) ∨ (¬ p79) ∨ (¬ p80) ∨ (¬ p81) ∨ (¬ p82)) : p71 ∨ p69 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p71) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p69) := fun hu => hn (Or.inr hu)
  have u2 : p78 := by
    rcases h24313 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p73 := by
    rcases h24314 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p74 := by
    rcases h24315 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p75 := by
    rcases h24316 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p76 := by
    rcases h24317 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p77) := by
    rcases h280 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p79 := by
    rcases h390 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p80 := by
    rcases h391 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p81 := by
    rcases h392 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p82 := by
    rcases h393 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h305 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step24319 (p1140 p1163 p1171 p1172 p1173 p1174 p1175 p1179 : Prop)
    (h6997 : p1171 ∨ p1179)
    (h7002 : p1172 ∨ p1179)
    (h7007 : p1173 ∨ p1179)
    (h7012 : p1174 ∨ p1179)
    (h7017 : p1175 ∨ p1179)
    (h6896 : p1140 ∨ p1163 ∨ (¬ p1171) ∨ (¬ p1172) ∨ (¬ p1173) ∨ (¬ p1174) ∨ (¬ p1175)) : p1179 ∨ p1163 ∨ p1140 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1179) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1171 := by
    rcases h6997 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1172 := by
    rcases h7002 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1173 := by
    rcases h7007 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1174 := by
    rcases h7012 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1175 := by
    rcases h7017 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6896 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24320 (p1140 p1163 p1171 p1176 p1177 p1178 p1179 p1180 : Prop)
    (h24319 : p1179 ∨ p1163 ∨ p1140)
    (h6994 : p1171 ∨ p1176)
    (h6995 : p1171 ∨ p1177)
    (h6996 : p1171 ∨ p1178)
    (h6998 : p1171 ∨ p1180)
    (h6921 : p1140 ∨ p1163 ∨ (¬ p1176) ∨ (¬ p1177) ∨ (¬ p1178) ∨ (¬ p1179) ∨ (¬ p1180)) : p1171 ∨ p1163 ∨ p1140 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1171) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1179 := by
    rcases h24319 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1176 := by
    rcases h6994 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1177 := by
    rcases h6995 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1178 := by
    rcases h6996 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1180 := by
    rcases h6998 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6921 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24321 (p1140 p1163 p1172 p1176 p1177 p1178 p1179 p1180 : Prop)
    (h24319 : p1179 ∨ p1163 ∨ p1140)
    (h6999 : p1172 ∨ p1176)
    (h7000 : p1172 ∨ p1177)
    (h7001 : p1172 ∨ p1178)
    (h7003 : p1172 ∨ p1180)
    (h6921 : p1140 ∨ p1163 ∨ (¬ p1176) ∨ (¬ p1177) ∨ (¬ p1178) ∨ (¬ p1179) ∨ (¬ p1180)) : p1172 ∨ p1163 ∨ p1140 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1172) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1179 := by
    rcases h24319 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1176 := by
    rcases h6999 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1177 := by
    rcases h7000 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1178 := by
    rcases h7001 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1180 := by
    rcases h7003 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6921 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24322 (p1140 p1163 p1173 p1176 p1177 p1178 p1179 p1180 : Prop)
    (h24319 : p1179 ∨ p1163 ∨ p1140)
    (h7004 : p1173 ∨ p1176)
    (h7005 : p1173 ∨ p1177)
    (h7006 : p1173 ∨ p1178)
    (h7008 : p1173 ∨ p1180)
    (h6921 : p1140 ∨ p1163 ∨ (¬ p1176) ∨ (¬ p1177) ∨ (¬ p1178) ∨ (¬ p1179) ∨ (¬ p1180)) : p1173 ∨ p1163 ∨ p1140 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1173) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1179 := by
    rcases h24319 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1176 := by
    rcases h7004 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1177 := by
    rcases h7005 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1178 := by
    rcases h7006 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1180 := by
    rcases h7008 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6921 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24323 (p1140 p1163 p1174 p1176 p1177 p1178 p1179 p1180 : Prop)
    (h24319 : p1179 ∨ p1163 ∨ p1140)
    (h7009 : p1174 ∨ p1176)
    (h7010 : p1174 ∨ p1177)
    (h7011 : p1174 ∨ p1178)
    (h7013 : p1174 ∨ p1180)
    (h6921 : p1140 ∨ p1163 ∨ (¬ p1176) ∨ (¬ p1177) ∨ (¬ p1178) ∨ (¬ p1179) ∨ (¬ p1180)) : p1174 ∨ p1163 ∨ p1140 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1174) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1179 := by
    rcases h24319 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1176 := by
    rcases h7009 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1177 := by
    rcases h7010 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1178 := by
    rcases h7011 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1180 := by
    rcases h7013 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6921 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24324 (p4 p8 p11 p15 p17 p18 p21 p25 p43 p45 p47 p49 p63 p69 p71 p85 p101 p126 p137 p142 p160 p161 p189 p193 p194 p224 p256 p258 p268 p286 p287 p288 p301 p310 p344 p346 p423 p434 p438 p495 p499 p633 p635 p636 p640 p657 p662 p666 p668 p680 p710 p713 p728 p734 p834 p835 p836 p840 p858 p862 p880 p884 p897 p904 p918 p923 p927 p928 p980 p983 p1035 p1036 p1044 p1076 p1077 p1095 p1096 p1098 p1099 p1115 p1116 p1140 p1141 p1159 p1163 p1167 p1171 p1172 p1173 p1174 p1175 p1176 p1177 p1178 p1179 p1180 p1206 p1212 p1213 p1225 p1226 p1229 p1249 p1274 p1306 p1330 p1333 p1385 p1465 : Prop)
    (h21511 : p1098 ∨ p1096)
    (h20854 : p710 ∨ p713)
    (h23161 : p680 ∨ p710)
    (h7050 : (¬ p680) ∨ (¬ p713) ∨ (¬ p897) ∨ (¬ p1098))
    (h20784 : p897 ∨ p904)
    (h17203 : p668 ∨ (¬ p904))
    (h22986 : p710 ∨ p8)
    (h24278 : p268 ∨ p17)
    (h21276 : p256 ∨ p17)
    (h9367 : p1096 ∨ (¬ p1229) ∨ (¬ p1306))
    (h23906 : p1306 ∨ p1095)
    (h24237 : (¬ p1076) ∨ p1096 ∨ (¬ p1229))
    (h21482 : p1077 ∨ p1076)
    (h21802 : p1096 ∨ p1099)
    (h22560 : p346 ∨ p344)
    (h22566 : p4 ∨ p344)
    (h12376 : p344 ∨ (¬ p662) ∨ (¬ p1077))
    (h11229 : p344 ∨ (¬ p635) ∨ (¬ p904))
    (h19489 : (¬ p8) ∨ (¬ p346) ∨ (¬ p983) ∨ (¬ p1077))
    (h16441 : (¬ p8) ∨ (¬ p258) ∨ (¬ p268) ∨ (¬ p310) ∨ (¬ p346))
    (h21721 : p662 ∨ p657)
    (h21505 : p633 ∨ p635)
    (h20687 : p980 ∨ p983)
    (h21140 : p286 ∨ p258)
    (h21436 : p258 ∨ p287)
    (h21668 : p258 ∨ p288)
    (h21866 : p258 ∨ (¬ p1077) ∨ (¬ p11))
    (h6747 : (¬ p224) ∨ (¬ p657))
    (h11291 : (¬ p633) ∨ (¬ p636))
    (h13257 : (¬ p286) ∨ (¬ p1077) ∨ p1116)
    (h16501 : (¬ p256) ∨ (¬ p287) ∨ (¬ p346) ∨ (¬ p840) ∨ (¬ p1077))
    (h18095 : (¬ p189) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p1077))
    (h16562 : (¬ p4) ∨ (¬ p288) ∨ (¬ p301) ∨ (¬ p668) ∨ (¬ p1077))
    (h22413 : p666 ∨ p224)
    (h12014 : (¬ p1115) ∨ (¬ p1116))
    (h21988 : p840 ∨ p836)
    (h22305 : p834 ∨ p840)
    (h22858 : p835 ∨ p840)
    (h14730 : p840 ∨ (¬ p904) ∨ (¬ p923))
    (h21262 : p189 ∨ p193)
    (h20973 : p301 ∨ p126)
    (h15453 : (¬ p666) ∨ p983 ∨ (¬ p1333))
    (h12570 : (¬ p666) ∨ (¬ p834) ∨ (¬ p858) ∨ p1115)
    (h22420 : (¬ p734) ∨ p224 ∨ (¬ p836) ∨ (¬ p1116))
    (h22484 : p923 ∨ p928)
    (h24099 : p194 ∨ (¬ p193))
    (h21644 : p1330 ∨ p1333)
    (h21694 : p858 ∨ p862)
    (h20753 : p728 ∨ p734)
    (h7049 : (¬ p918) ∨ (¬ p928))
    (h20211 : (¬ p668) ∨ (¬ p835) ∨ (¬ p928) ∨ (¬ p1116) ∨ (¬ p1385))
    (h15694 : (¬ p862) ∨ (¬ p1249) ∨ p1385)
    (h23007 : (¬ p904) ∨ (¬ p438) ∨ (¬ p728) ∨ p344)
    (h23359 : p927 ∨ p918)
    (h23105 : p1274 ∨ p1249)
    (h21060 : p438 ∨ p434)
    (h13650 : (¬ p63) ∨ (¬ p927) ∨ (¬ p1099))
    (h12049 : p85 ∨ (¬ p927) ∨ (¬ p1099))
    (h17359 : (¬ p45) ∨ (¬ p193) ∨ (¬ p836) ∨ (¬ p904) ∨ (¬ p927))
    (h18105 : (¬ p85) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p1077))
    (h16576 : (¬ p85) ∨ (¬ p980) ∨ (¬ p1225) ∨ (¬ p1229))
    (h22129 : p45 ∨ p47)
    (h20942 : p495 ∨ p499)
    (h21572 : p161 ∨ p1225)
    (h23106 : (¬ p160) ∨ (¬ p161) ∨ (¬ p85) ∨ (¬ p1274))
    (h21183 : p1226 ∨ p160)
    (h24301 : p640 ∨ p636)
    (h24307 : (¬ p142) ∨ (¬ p640) ∨ (¬ p47) ∨ (¬ p193) ∨ (¬ p346) ∨ (¬ p904) ∨ (¬ p1077))
    (h24306 : p142 ∨ p137)
    (h15482 : p11 ∨ (¬ p137) ∨ (¬ p1206))
    (h15428 : (¬ p101) ∨ (¬ p137) ∨ p258)
    (h21957 : p1212 ∨ p1206)
    (h24268 : p1213 ∨ p1206)
    (h24310 : p18 ∨ (¬ p1212) ∨ p101 ∨ p142 ∨ (¬ p1274) ∨ p189 ∨ (¬ p346) ∨ (¬ p668) ∨ (¬ p1077) ∨ (¬ p1229))
    (h24312 : (¬ p69) ∨ (¬ p18) ∨ (¬ p1213) ∨ (¬ p1229))
    (h21946 : p69 ∨ p15)
    (h5072 : (¬ p15) ∨ (¬ p25) ∨ (¬ p495))
    (h8753 : (¬ p15) ∨ (¬ p884) ∨ (¬ p1099))
    (h12953 : (¬ p15) ∨ (¬ p43) ∨ p63)
    (h23917 : p21 ∨ p25)
    (h23127 : p884 ∨ p880)
    (h22271 : p49 ∨ p43)
    (h18211 : (¬ p15) ∨ (¬ p21) ∨ (¬ p423) ∨ (¬ p495) ∨ (¬ p1213))
    (h10694 : (¬ p880) ∨ (¬ p1036) ∨ (¬ p1095))
    (h20723 : p423 ∨ p1141)
    (h21840 : p1044 ∨ p1036)
    (h24318 : p71 ∨ p69)
    (h18212 : (¬ p49) ∨ (¬ p71) ∨ (¬ p85) ∨ (¬ p1140) ∨ (¬ p1141))
    (h21650 : p1159 ∨ p1140)
    (h18213 : (¬ p126) ∨ (¬ p194) ∨ (¬ p256) ∨ (¬ p434) ∨ (¬ p1159) ∨ (¬ p1330) ∨ (¬ p1465))
    (h21566 : p1465 ∨ p1035)
    (h18214 : (¬ p194) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p1035) ∨ (¬ p1044) ∨ (¬ p1077) ∨ (¬ p1163) ∨ (¬ p1226))
    (h11185 : p160 ∨ (¬ p1035) ∨ (¬ p1167))
    (h24319 : p1179 ∨ p1163 ∨ p1140)
    (h24320 : p1171 ∨ p1163 ∨ p1140)
    (h24321 : p1172 ∨ p1163 ∨ p1140)
    (h24322 : p1173 ∨ p1163 ∨ p1140)
    (h24323 : p1174 ∨ p1163 ∨ p1140)
    (h6894 : p1163 ∨ p1167 ∨ (¬ p1171) ∨ (¬ p1172) ∨ (¬ p1173) ∨ (¬ p1174) ∨ (¬ p1175))
    (h7014 : p1175 ∨ p1176)
    (h7015 : p1175 ∨ p1177)
    (h7016 : p1175 ∨ p1178)
    (h7018 : p1175 ∨ p1180)
    (h6921 : p1140 ∨ p1163 ∨ (¬ p1176) ∨ (¬ p1177) ∨ (¬ p1178) ∨ (¬ p1179) ∨ (¬ p1180)) : p344 ∨ p710 ∨ (¬ p310) ∨ p17 ∨ p1096 ∨ (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p344) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p710) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1098 := by
    rcases h21511 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u7 : p713 := by
    rcases h20854 with q0 | q1
    · exact False.elim (u1 q0)
    · exact q1
  have u8 : p680 := by
    rcases h23161 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : (¬ p897) := by
    rcases h7050 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u8)
    · exact False.elim (q1 u7)
    · exact q2
    · exact False.elim (q3 u6)
  have u10 : p904 := by
    rcases h20784 with q0 | q1
    · exact False.elim (u9 q0)
    · exact q1
  have u11 : p668 := by
    rcases h17203 with q0 | q1
    · exact q0
    · exact False.elim (q1 u10)
  have u12 : p8 := by
    rcases h22986 with q0 | q1
    · exact False.elim (u1 q0)
    · exact q1
  have u13 : p268 := by
    rcases h24278 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u14 : p256 := by
    rcases h21276 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u15 : (¬ p1306) := by
    rcases h9367 with q0 | q1 | q2
    · exact False.elim (u4 q0)
    · exact False.elim (q1 u5)
    · exact q2
  have u16 : p1095 := by
    rcases h23906 with q0 | q1
    · exact False.elim (u15 q0)
    · exact q1
  have u17 : (¬ p1076) := by
    rcases h24237 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u4 q1)
    · exact False.elim (q2 u5)
  have u18 : p1077 := by
    rcases h21482 with q0 | q1
    · exact q0
    · exact False.elim (u17 q1)
  have u19 : p1099 := by
    rcases h21802 with q0 | q1
    · exact False.elim (u4 q0)
    · exact q1
  have u20 : p346 := by
    rcases h22560 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u21 : p4 := by
    rcases h22566 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u22 : (¬ p662) := by
    rcases h12376 with q0 | q1 | q2
    · exact False.elim (u0 q0)
    · exact q1
    · exact False.elim (q2 u18)
  have u23 : (¬ p635) := by
    rcases h11229 with q0 | q1 | q2
    · exact False.elim (u0 q0)
    · exact q1
    · exact False.elim (q2 u10)
  have u24 : (¬ p983) := by
    rcases h19489 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u12)
    · exact False.elim (q1 u20)
    · exact q2
    · exact False.elim (q3 u18)
  have u25 : (¬ p258) := by
    rcases h16441 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u12)
    · exact q1
    · exact False.elim (q2 u13)
    · exact False.elim (q3 u2)
    · exact False.elim (q4 u20)
  have u26 : p657 := by
    rcases h21721 with q0 | q1
    · exact False.elim (u22 q0)
    · exact q1
  have u27 : p633 := by
    rcases h21505 with q0 | q1
    · exact q0
    · exact False.elim (u23 q1)
  have u28 : p980 := by
    rcases h20687 with q0 | q1
    · exact q0
    · exact False.elim (u24 q1)
  have u29 : p286 := by
    rcases h21140 with q0 | q1
    · exact q0
    · exact False.elim (u25 q1)
  have u30 : p287 := by
    rcases h21436 with q0 | q1
    · exact False.elim (u25 q0)
    · exact q1
  have u31 : p288 := by
    rcases h21668 with q0 | q1
    · exact False.elim (u25 q0)
    · exact q1
  have u32 : (¬ p11) := by
    rcases h21866 with q0 | q1 | q2
    · exact False.elim (u25 q0)
    · exact False.elim (q1 u18)
    · exact q2
  have u33 : (¬ p224) := by
    rcases h6747 with q0 | q1
    · exact q0
    · exact False.elim (q1 u26)
  have u34 : (¬ p636) := by
    rcases h11291 with q0 | q1
    · exact False.elim (q0 u27)
    · exact q1
  have u35 : p1116 := by
    rcases h13257 with q0 | q1 | q2
    · exact False.elim (q0 u29)
    · exact False.elim (q1 u18)
    · exact q2
  have u36 : (¬ p840) := by
    rcases h16501 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u14)
    · exact False.elim (q1 u30)
    · exact False.elim (q2 u20)
    · exact q3
    · exact False.elim (q4 u18)
  have u37 : (¬ p189) := by
    rcases h18095 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u14)
    · exact False.elim (q2 u31)
    · exact False.elim (q3 u18)
  have u38 : (¬ p301) := by
    rcases h16562 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u21)
    · exact False.elim (q1 u31)
    · exact q2
    · exact False.elim (q3 u11)
    · exact False.elim (q4 u18)
  have u39 : p666 := by
    rcases h22413 with q0 | q1
    · exact q0
    · exact False.elim (u33 q1)
  have u40 : (¬ p1115) := by
    rcases h12014 with q0 | q1
    · exact q0
    · exact False.elim (q1 u35)
  have u41 : p836 := by
    rcases h21988 with q0 | q1
    · exact False.elim (u36 q0)
    · exact q1
  have u42 : p834 := by
    rcases h22305 with q0 | q1
    · exact q0
    · exact False.elim (u36 q1)
  have u43 : p835 := by
    rcases h22858 with q0 | q1
    · exact q0
    · exact False.elim (u36 q1)
  have u44 : (¬ p923) := by
    rcases h14730 with q0 | q1 | q2
    · exact False.elim (u36 q0)
    · exact False.elim (q1 u10)
    · exact q2
  have u45 : p193 := by
    rcases h21262 with q0 | q1
    · exact False.elim (u37 q0)
    · exact q1
  have u46 : p126 := by
    rcases h20973 with q0 | q1
    · exact False.elim (u38 q0)
    · exact q1
  have u47 : (¬ p1333) := by
    rcases h15453 with q0 | q1 | q2
    · exact False.elim (q0 u39)
    · exact False.elim (u24 q1)
    · exact q2
  have u48 : (¬ p858) := by
    rcases h12570 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u39)
    · exact False.elim (q1 u42)
    · exact q2
    · exact False.elim (u40 q3)
  have u49 : (¬ p734) := by
    rcases h22420 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (u33 q1)
    · exact False.elim (q2 u41)
    · exact False.elim (q3 u35)
  have u50 : p928 := by
    rcases h22484 with q0 | q1
    · exact False.elim (u44 q0)
    · exact q1
  have u51 : p194 := by
    rcases h24099 with q0 | q1
    · exact q0
    · exact False.elim (q1 u45)
  have u52 : p1330 := by
    rcases h21644 with q0 | q1
    · exact q0
    · exact False.elim (u47 q1)
  have u53 : p862 := by
    rcases h21694 with q0 | q1
    · exact False.elim (u48 q0)
    · exact q1
  have u54 : p728 := by
    rcases h20753 with q0 | q1
    · exact q0
    · exact False.elim (u49 q1)
  have u55 : (¬ p918) := by
    rcases h7049 with q0 | q1
    · exact q0
    · exact False.elim (q1 u50)
  have u56 : (¬ p1385) := by
    rcases h20211 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u11)
    · exact False.elim (q1 u43)
    · exact False.elim (q2 u50)
    · exact False.elim (q3 u35)
    · exact q4
  have u57 : (¬ p1249) := by
    rcases h15694 with q0 | q1 | q2
    · exact False.elim (q0 u53)
    · exact q1
    · exact False.elim (u56 q2)
  have u58 : (¬ p438) := by
    rcases h23007 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u10)
    · exact q1
    · exact False.elim (q2 u54)
    · exact False.elim (u0 q3)
  have u59 : p927 := by
    rcases h23359 with q0 | q1
    · exact q0
    · exact False.elim (u55 q1)
  have u60 : p1274 := by
    rcases h23105 with q0 | q1
    · exact q0
    · exact False.elim (u57 q1)
  have u61 : p434 := by
    rcases h21060 with q0 | q1
    · exact False.elim (u58 q0)
    · exact q1
  have u62 : (¬ p63) := by
    rcases h13650 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u59)
    · exact False.elim (q2 u19)
  have u63 : p85 := by
    rcases h12049 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u59)
    · exact False.elim (q2 u19)
  have u64 : (¬ p45) := by
    rcases h17359 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u45)
    · exact False.elim (q2 u41)
    · exact False.elim (q3 u10)
    · exact False.elim (q4 u59)
  have u65 : (¬ p499) := by
    rcases h18105 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u63)
    · exact q1
    · exact False.elim (q2 u27)
    · exact False.elim (q3 u18)
  have u66 : (¬ p1225) := by
    rcases h16576 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u63)
    · exact False.elim (q1 u28)
    · exact q2
    · exact False.elim (q3 u5)
  have u67 : p47 := by
    rcases h22129 with q0 | q1
    · exact False.elim (u64 q0)
    · exact q1
  have u68 : p495 := by
    rcases h20942 with q0 | q1
    · exact q0
    · exact False.elim (u65 q1)
  have u69 : p161 := by
    rcases h21572 with q0 | q1
    · exact q0
    · exact False.elim (u66 q1)
  have u70 : (¬ p160) := by
    rcases h23106 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u69)
    · exact False.elim (q2 u63)
    · exact False.elim (q3 u60)
  have u71 : p1226 := by
    rcases h21183 with q0 | q1
    · exact q0
    · exact False.elim (u70 q1)
  have u72 : p640 := by
    rcases h24301 with q0 | q1
    · exact q0
    · exact False.elim (u34 q1)
  have u73 : (¬ p142) := by
    rcases h24307 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact q0
    · exact False.elim (q1 u72)
    · exact False.elim (q2 u67)
    · exact False.elim (q3 u45)
    · exact False.elim (q4 u20)
    · exact False.elim (q5 u10)
    · exact False.elim (q6 u18)
  have u74 : p137 := by
    rcases h24306 with q0 | q1
    · exact False.elim (u73 q0)
    · exact q1
  have u75 : (¬ p1206) := by
    rcases h15482 with q0 | q1 | q2
    · exact False.elim (u32 q0)
    · exact False.elim (q1 u74)
    · exact q2
  have u76 : (¬ p101) := by
    rcases h15428 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u74)
    · exact False.elim (u25 q2)
  have u77 : p1212 := by
    rcases h21957 with q0 | q1
    · exact q0
    · exact False.elim (u75 q1)
  have u78 : p1213 := by
    rcases h24268 with q0 | q1
    · exact q0
    · exact False.elim (u75 q1)
  have u79 : p18 := by
    rcases h24310 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
    · exact q0
    · exact False.elim (q1 u77)
    · exact False.elim (u76 q2)
    · exact False.elim (u73 q3)
    · exact False.elim (q4 u60)
    · exact False.elim (u37 q5)
    · exact False.elim (q6 u20)
    · exact False.elim (q7 u11)
    · exact False.elim (q8 u18)
    · exact False.elim (q9 u5)
  have u80 : (¬ p69) := by
    rcases h24312 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u79)
    · exact False.elim (q2 u78)
    · exact False.elim (q3 u5)
  have u81 : p15 := by
    rcases h21946 with q0 | q1
    · exact False.elim (u80 q0)
    · exact q1
  have u82 : (¬ p25) := by
    rcases h5072 with q0 | q1 | q2
    · exact False.elim (q0 u81)
    · exact q1
    · exact False.elim (q2 u68)
  have u83 : (¬ p884) := by
    rcases h8753 with q0 | q1 | q2
    · exact False.elim (q0 u81)
    · exact q1
    · exact False.elim (q2 u19)
  have u84 : (¬ p43) := by
    rcases h12953 with q0 | q1 | q2
    · exact False.elim (q0 u81)
    · exact q1
    · exact False.elim (u62 q2)
  have u85 : p21 := by
    rcases h23917 with q0 | q1
    · exact q0
    · exact False.elim (u82 q1)
  have u86 : p880 := by
    rcases h23127 with q0 | q1
    · exact False.elim (u83 q0)
    · exact q1
  have u87 : p49 := by
    rcases h22271 with q0 | q1
    · exact q0
    · exact False.elim (u84 q1)
  have u88 : (¬ p423) := by
    rcases h18211 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u81)
    · exact False.elim (q1 u85)
    · exact q2
    · exact False.elim (q3 u68)
    · exact False.elim (q4 u78)
  have u89 : (¬ p1036) := by
    rcases h10694 with q0 | q1 | q2
    · exact False.elim (q0 u86)
    · exact q1
    · exact False.elim (q2 u16)
  have u90 : p1141 := by
    rcases h20723 with q0 | q1
    · exact False.elim (u88 q0)
    · exact q1
  have u91 : p1044 := by
    rcases h21840 with q0 | q1
    · exact q0
    · exact False.elim (u89 q1)
  have u92 : p71 := by
    rcases h24318 with q0 | q1
    · exact q0
    · exact False.elim (u80 q1)
  have u93 : (¬ p1140) := by
    rcases h18212 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u87)
    · exact False.elim (q1 u92)
    · exact False.elim (q2 u63)
    · exact q3
    · exact False.elim (q4 u90)
  have u94 : p1159 := by
    rcases h21650 with q0 | q1
    · exact q0
    · exact False.elim (u93 q1)
  have u95 : (¬ p1465) := by
    rcases h18213 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u46)
    · exact False.elim (q1 u51)
    · exact False.elim (q2 u14)
    · exact False.elim (q3 u61)
    · exact False.elim (q4 u94)
    · exact False.elim (q5 u52)
    · exact q6
  have u96 : p1035 := by
    rcases h21566 with q0 | q1
    · exact False.elim (u95 q0)
    · exact q1
  have u97 : (¬ p1163) := by
    rcases h18214 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
    · exact False.elim (q0 u51)
    · exact False.elim (q1 u14)
    · exact False.elim (q2 u31)
    · exact False.elim (q3 u96)
    · exact False.elim (q4 u91)
    · exact False.elim (q5 u18)
    · exact q6
    · exact False.elim (q7 u71)
  have u98 : (¬ p1167) := by
    rcases h11185 with q0 | q1 | q2
    · exact False.elim (u70 q0)
    · exact False.elim (q1 u96)
    · exact q2
  have u99 : p1179 := by
    rcases h24319 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u97 q1)
    · exact False.elim (u93 q2)
  have u100 : p1171 := by
    rcases h24320 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u97 q1)
    · exact False.elim (u93 q2)
  have u101 : p1172 := by
    rcases h24321 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u97 q1)
    · exact False.elim (u93 q2)
  have u102 : p1173 := by
    rcases h24322 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u97 q1)
    · exact False.elim (u93 q2)
  have u103 : p1174 := by
    rcases h24323 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u97 q1)
    · exact False.elim (u93 q2)
  have u104 : (¬ p1175) := by
    rcases h6894 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u97 q0)
    · exact False.elim (u98 q1)
    · exact False.elim (q2 u100)
    · exact False.elim (q3 u101)
    · exact False.elim (q4 u102)
    · exact False.elim (q5 u103)
    · exact q6
  have u105 : p1176 := by
    rcases h7014 with q0 | q1
    · exact False.elim (u104 q0)
    · exact q1
  have u106 : p1177 := by
    rcases h7015 with q0 | q1
    · exact False.elim (u104 q0)
    · exact q1
  have u107 : p1178 := by
    rcases h7016 with q0 | q1
    · exact False.elim (u104 q0)
    · exact q1
  have u108 : p1180 := by
    rcases h7018 with q0 | q1
    · exact False.elim (u104 q0)
    · exact q1
  rcases h6921 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u93 q0)
  · exact False.elim (u97 q1)
  · exact False.elim (q2 u105)
  · exact False.elim (q3 u106)
  · exact False.elim (q4 u107)
  · exact False.elim (q5 u99)
  · exact False.elim (q6 u108)

theorem step24325 (p160 p189 p193 p194 p256 p288 p1035 p1044 p1077 p1140 p1163 p1167 p1171 p1172 p1173 p1174 p1175 p1176 p1177 p1178 p1179 p1180 p1226 : Prop)
    (h21183 : p1226 ∨ p160)
    (h18095 : (¬ p189) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p1077))
    (h21262 : p189 ∨ p193)
    (h24099 : p194 ∨ (¬ p193))
    (h18214 : (¬ p194) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p1035) ∨ (¬ p1044) ∨ (¬ p1077) ∨ (¬ p1163) ∨ (¬ p1226))
    (h11185 : p160 ∨ (¬ p1035) ∨ (¬ p1167))
    (h24319 : p1179 ∨ p1163 ∨ p1140)
    (h24320 : p1171 ∨ p1163 ∨ p1140)
    (h24321 : p1172 ∨ p1163 ∨ p1140)
    (h24322 : p1173 ∨ p1163 ∨ p1140)
    (h24323 : p1174 ∨ p1163 ∨ p1140)
    (h6894 : p1163 ∨ p1167 ∨ (¬ p1171) ∨ (¬ p1172) ∨ (¬ p1173) ∨ (¬ p1174) ∨ (¬ p1175))
    (h7014 : p1175 ∨ p1176)
    (h7015 : p1175 ∨ p1177)
    (h7016 : p1175 ∨ p1178)
    (h7018 : p1175 ∨ p1180)
    (h6921 : p1140 ∨ p1163 ∨ (¬ p1176) ∨ (¬ p1177) ∨ (¬ p1178) ∨ (¬ p1179) ∨ (¬ p1180)) : (¬ p1035) ∨ (¬ p1044) ∨ p1140 ∨ p160 ∨ (¬ p288) ∨ (¬ p256) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1044 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p160) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1226 := by
    rcases h21183 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : (¬ p189) := by
    rcases h18095 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u5)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u6)
  have u9 : p193 := by
    rcases h21262 with q0 | q1
    · exact False.elim (u8 q0)
    · exact q1
  have u10 : p194 := by
    rcases h24099 with q0 | q1
    · exact q0
    · exact False.elim (q1 u9)
  have u11 : (¬ p1163) := by
    rcases h18214 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
    · exact False.elim (q0 u10)
    · exact False.elim (q1 u5)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u6)
    · exact q6
    · exact False.elim (q7 u7)
  have u12 : (¬ p1167) := by
    rcases h11185 with q0 | q1 | q2
    · exact False.elim (u3 q0)
    · exact False.elim (q1 u0)
    · exact q2
  have u13 : p1179 := by
    rcases h24319 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u11 q1)
    · exact False.elim (u2 q2)
  have u14 : p1171 := by
    rcases h24320 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u11 q1)
    · exact False.elim (u2 q2)
  have u15 : p1172 := by
    rcases h24321 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u11 q1)
    · exact False.elim (u2 q2)
  have u16 : p1173 := by
    rcases h24322 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u11 q1)
    · exact False.elim (u2 q2)
  have u17 : p1174 := by
    rcases h24323 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u11 q1)
    · exact False.elim (u2 q2)
  have u18 : (¬ p1175) := by
    rcases h6894 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u11 q0)
    · exact False.elim (u12 q1)
    · exact False.elim (q2 u14)
    · exact False.elim (q3 u15)
    · exact False.elim (q4 u16)
    · exact False.elim (q5 u17)
    · exact q6
  have u19 : p1176 := by
    rcases h7014 with q0 | q1
    · exact False.elim (u18 q0)
    · exact q1
  have u20 : p1177 := by
    rcases h7015 with q0 | q1
    · exact False.elim (u18 q0)
    · exact q1
  have u21 : p1178 := by
    rcases h7016 with q0 | q1
    · exact False.elim (u18 q0)
    · exact q1
  have u22 : p1180 := by
    rcases h7018 with q0 | q1
    · exact False.elim (u18 q0)
    · exact q1
  rcases h6921 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u11 q1)
  · exact False.elim (q2 u19)
  · exact False.elim (q3 u20)
  · exact False.elim (q4 u21)
  · exact False.elim (q5 u13)
  · exact False.elim (q6 u22)

theorem step24326 (p303 p595 p603 p616 p1229 p1288 p1292 : Prop)
    (h21790 : p616 ∨ p595)
    (h10625 : p595 ∨ (¬ p1229) ∨ (¬ p1288))
    (h16662 : (¬ p303) ∨ (¬ p603) ∨ (¬ p616) ∨ (¬ p1229) ∨ (¬ p1292))
    (h20807 : p1292 ∨ p1288) : p595 ∨ (¬ p303) ∨ (¬ p603) ∨ (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p595) := fun hu => hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p603 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p616 := by
    rcases h21790 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : (¬ p1288) := by
    rcases h10625 with q0 | q1 | q2
    · exact False.elim (u0 q0)
    · exact False.elim (q1 u3)
    · exact q2
  have u6 : (¬ p1292) := by
    rcases h16662 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u1)
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u3)
    · exact q4
  rcases h20807 with q0 | q1
  · exact False.elim (u6 q0)
  · exact False.elim (u5 q1)

theorem step24327 (p15 p18 p21 p25 p234 p324 p330 p495 : Prop)
    (h5072 : (¬ p15) ∨ (¬ p25) ∨ (¬ p495))
    (h23949 : p25 ∨ p18)
    (h23917 : p21 ∨ p25)
    (h16636 : (¬ p15) ∨ (¬ p21) ∨ (¬ p234) ∨ (¬ p330) ∨ (¬ p495))
    (h10847 : (¬ p18) ∨ (¬ p234) ∨ (¬ p324))
    (h24257 : p330 ∨ p324) : (¬ p234) ∨ (¬ p15) ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p25) := by
    rcases h5072 with q0 | q1 | q2
    · exact False.elim (q0 u1)
    · exact q1
    · exact False.elim (q2 u2)
  have u4 : p18 := by
    rcases h23949 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  have u5 : p21 := by
    rcases h23917 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : (¬ p330) := by
    rcases h16636 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u1)
    · exact False.elim (q1 u5)
    · exact False.elim (q2 u0)
    · exact q3
    · exact False.elim (q4 u2)
  have u7 : (¬ p324) := by
    rcases h10847 with q0 | q1 | q2
    · exact False.elim (q0 u4)
    · exact False.elim (q1 u0)
    · exact q2
  rcases h24257 with q0 | q1
  · exact False.elim (u6 q0)
  · exact False.elim (u7 q1)

theorem step24328 (p194 p256 p288 p344 p382 p419 p477 p480 p545 p996 : Prop)
    (h21954 : p419 ∨ p996)
    (h11746 : (¬ p382) ∨ p419 ∨ (¬ p480))
    (h18101 : (¬ p194) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p382) ∨ (¬ p477) ∨ (¬ p545) ∨ (¬ p996))
    (h21305 : p477 ∨ p480) : p419 ∨ (¬ p545) ∨ (¬ p382) ∨ (¬ p194) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p194 := by
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
  have u6 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p996 := by
    rcases h21954 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u8 : (¬ p480) := by
    rcases h11746 with q0 | q1 | q2
    · exact False.elim (q0 u2)
    · exact False.elim (u0 q1)
    · exact q2
  have u9 : (¬ p477) := by
    rcases h18101 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
    · exact False.elim (q0 u3)
    · exact False.elim (q1 u6)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u2)
    · exact q5
    · exact False.elim (q6 u1)
    · exact False.elim (q7 u7)
  rcases h21305 with q0 | q1
  · exact False.elim (u9 q0)
  · exact False.elim (u8 q1)

theorem step24329 (p384 p387 p390 p391 p392 p393 p394 p398 : Prop)
    (h2184 : p390 ∨ p398)
    (h2189 : p391 ∨ p398)
    (h2194 : p392 ∨ p398)
    (h2199 : p393 ∨ p398)
    (h2204 : p394 ∨ p398)
    (h2088 : p384 ∨ p387 ∨ (¬ p390) ∨ (¬ p391) ∨ (¬ p392) ∨ (¬ p393) ∨ (¬ p394)) : p398 ∨ p384 ∨ p387 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p398) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p384) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p387) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p390 := by
    rcases h2184 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p391 := by
    rcases h2189 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p392 := by
    rcases h2194 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p393 := by
    rcases h2199 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p394 := by
    rcases h2204 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2088 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24330 (p384 p387 p390 p395 p396 p397 p398 p399 : Prop)
    (h24329 : p398 ∨ p384 ∨ p387)
    (h2181 : p390 ∨ p395)
    (h2182 : p390 ∨ p396)
    (h2183 : p390 ∨ p397)
    (h2185 : p390 ∨ p399)
    (h2113 : p384 ∨ p387 ∨ (¬ p395) ∨ (¬ p396) ∨ (¬ p397) ∨ (¬ p398) ∨ (¬ p399)) : p390 ∨ p384 ∨ p387 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p390) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p384) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p387) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p398 := by
    rcases h24329 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p395 := by
    rcases h2181 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p396 := by
    rcases h2182 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p397 := by
    rcases h2183 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p399 := by
    rcases h2185 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2113 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24331 (p384 p387 p391 p395 p396 p397 p398 p399 : Prop)
    (h24329 : p398 ∨ p384 ∨ p387)
    (h2186 : p391 ∨ p395)
    (h2187 : p391 ∨ p396)
    (h2188 : p391 ∨ p397)
    (h2190 : p391 ∨ p399)
    (h2113 : p384 ∨ p387 ∨ (¬ p395) ∨ (¬ p396) ∨ (¬ p397) ∨ (¬ p398) ∨ (¬ p399)) : p391 ∨ p384 ∨ p387 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p391) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p384) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p387) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p398 := by
    rcases h24329 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p395 := by
    rcases h2186 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p396 := by
    rcases h2187 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p397 := by
    rcases h2188 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p399 := by
    rcases h2190 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2113 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24332 (p384 p387 p392 p395 p396 p397 p398 p399 : Prop)
    (h24329 : p398 ∨ p384 ∨ p387)
    (h2191 : p392 ∨ p395)
    (h2192 : p392 ∨ p396)
    (h2193 : p392 ∨ p397)
    (h2195 : p392 ∨ p399)
    (h2113 : p384 ∨ p387 ∨ (¬ p395) ∨ (¬ p396) ∨ (¬ p397) ∨ (¬ p398) ∨ (¬ p399)) : p392 ∨ p384 ∨ p387 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p392) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p384) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p387) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p398 := by
    rcases h24329 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p395 := by
    rcases h2191 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p396 := by
    rcases h2192 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p397 := by
    rcases h2193 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p399 := by
    rcases h2195 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2113 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24333 (p384 p387 p390 p391 p392 p393 p394 p395 p396 p397 p398 p399 : Prop)
    (h21375 : p394 ∨ (¬ p398) ∨ p384 ∨ p387)
    (h24330 : p390 ∨ p384 ∨ p387)
    (h24331 : p391 ∨ p384 ∨ p387)
    (h24332 : p392 ∨ p384 ∨ p387)
    (h2088 : p384 ∨ p387 ∨ (¬ p390) ∨ (¬ p391) ∨ (¬ p392) ∨ (¬ p393) ∨ (¬ p394))
    (h2196 : p393 ∨ p395)
    (h2197 : p393 ∨ p396)
    (h2198 : p393 ∨ p397)
    (h2200 : p393 ∨ p399)
    (h2113 : p384 ∨ p387 ∨ (¬ p395) ∨ (¬ p396) ∨ (¬ p397) ∨ (¬ p398) ∨ (¬ p399)) : (¬ p398) ∨ p384 ∨ p387 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p398 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p384) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p387) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p394 := by
    rcases h21375 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u4 : p390 := by
    rcases h24330 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u5 : p391 := by
    rcases h24331 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u6 : p392 := by
    rcases h24332 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u7 : (¬ p393) := by
    rcases h2088 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u6)
    · exact q5
    · exact False.elim (q6 u3)
  have u8 : p395 := by
    rcases h2196 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p396 := by
    rcases h2197 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p397 := by
    rcases h2198 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p399 := by
    rcases h2200 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h2113 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u11)

theorem step24334 (p384 p387 p398 : Prop)
    (h24329 : p398 ∨ p384 ∨ p387)
    (h24333 : (¬ p398) ∨ p384 ∨ p387) : p384 ∨ p387 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p384) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p387) := fun hu => hn (Or.inr hu)
  have u2 : p398 := by
    rcases h24329 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h24333 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)

theorem step24335 (p346 p348 p352 p353 p354 p355 p356 p361 : Prop)
    (h1929 : p352 ∨ p361)
    (h1934 : p353 ∨ p361)
    (h1939 : p354 ∨ p361)
    (h1944 : p355 ∨ p361)
    (h1949 : p356 ∨ p361)
    (h1835 : p346 ∨ p348 ∨ (¬ p352) ∨ (¬ p353) ∨ (¬ p354) ∨ (¬ p355) ∨ (¬ p356)) : p361 ∨ p348 ∨ p346 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p361) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p348) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p346) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p352 := by
    rcases h1929 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p353 := by
    rcases h1934 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p354 := by
    rcases h1939 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p355 := by
    rcases h1944 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p356 := by
    rcases h1949 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1835 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24336 (p346 p348 p352 p357 p358 p359 p360 p361 : Prop)
    (h24335 : p361 ∨ p348 ∨ p346)
    (h1925 : p352 ∨ p357)
    (h1926 : p352 ∨ p358)
    (h1927 : p352 ∨ p359)
    (h1928 : p352 ∨ p360)
    (h1860 : p346 ∨ p348 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361)) : p352 ∨ p348 ∨ p346 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p352) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p348) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p346) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p361 := by
    rcases h24335 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p357 := by
    rcases h1925 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p358 := by
    rcases h1926 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p359 := by
    rcases h1927 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p360 := by
    rcases h1928 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1860 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step24337 (p346 p348 p353 p357 p358 p359 p360 p361 : Prop)
    (h24335 : p361 ∨ p348 ∨ p346)
    (h1930 : p353 ∨ p357)
    (h1931 : p353 ∨ p358)
    (h1932 : p353 ∨ p359)
    (h1933 : p353 ∨ p360)
    (h1860 : p346 ∨ p348 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361)) : p353 ∨ p348 ∨ p346 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p353) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p348) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p346) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p361 := by
    rcases h24335 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p357 := by
    rcases h1930 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p358 := by
    rcases h1931 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p359 := by
    rcases h1932 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p360 := by
    rcases h1933 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1860 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step24338 (p346 p348 p354 p357 p358 p359 p360 p361 : Prop)
    (h24335 : p361 ∨ p348 ∨ p346)
    (h1935 : p354 ∨ p357)
    (h1936 : p354 ∨ p358)
    (h1937 : p354 ∨ p359)
    (h1938 : p354 ∨ p360)
    (h1860 : p346 ∨ p348 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361)) : p354 ∨ p348 ∨ p346 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p354) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p348) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p346) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p361 := by
    rcases h24335 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p357 := by
    rcases h1935 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p358 := by
    rcases h1936 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p359 := by
    rcases h1937 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p360 := by
    rcases h1938 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1860 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step24339 (p346 p348 p355 p357 p358 p359 p360 p361 : Prop)
    (h24335 : p361 ∨ p348 ∨ p346)
    (h1940 : p355 ∨ p357)
    (h1941 : p355 ∨ p358)
    (h1942 : p355 ∨ p359)
    (h1943 : p355 ∨ p360)
    (h1860 : p346 ∨ p348 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361)) : p355 ∨ p348 ∨ p346 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p355) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p348) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p346) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p361 := by
    rcases h24335 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p357 := by
    rcases h1940 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p358 := by
    rcases h1941 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p359 := by
    rcases h1942 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p360 := by
    rcases h1943 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1860 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step24340 (p346 p348 p352 p353 p354 p355 p356 p357 p358 p359 p360 p361 : Prop)
    (h24335 : p361 ∨ p348 ∨ p346)
    (h24336 : p352 ∨ p348 ∨ p346)
    (h24337 : p353 ∨ p348 ∨ p346)
    (h24338 : p354 ∨ p348 ∨ p346)
    (h24339 : p355 ∨ p348 ∨ p346)
    (h1835 : p346 ∨ p348 ∨ (¬ p352) ∨ (¬ p353) ∨ (¬ p354) ∨ (¬ p355) ∨ (¬ p356))
    (h1945 : p356 ∨ p357)
    (h1946 : p356 ∨ p358)
    (h1947 : p356 ∨ p359)
    (h1948 : p356 ∨ p360)
    (h1860 : p346 ∨ p348 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361)) : p348 ∨ p346 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p348) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p346) := fun hu => hn (Or.inr hu)
  have u2 : p361 := by
    rcases h24335 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p352 := by
    rcases h24336 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p353 := by
    rcases h24337 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p354 := by
    rcases h24338 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p355 := by
    rcases h24339 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p356) := by
    rcases h1835 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p357 := by
    rcases h1945 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p358 := by
    rcases h1946 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p359 := by
    rcases h1947 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p360 := by
    rcases h1948 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h1860 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u2)

theorem step24341 (p477 p481 p484 p485 p486 p487 p488 p491 : Prop)
    (h2704 : p484 ∨ p491)
    (h2709 : p485 ∨ p491)
    (h2714 : p486 ∨ p491)
    (h2719 : p487 ∨ p491)
    (h2724 : p488 ∨ p491)
    (h2604 : p477 ∨ p481 ∨ (¬ p484) ∨ (¬ p485) ∨ (¬ p486) ∨ (¬ p487) ∨ (¬ p488)) : p491 ∨ p477 ∨ p481 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p491) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p477) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p481) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p484 := by
    rcases h2704 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p485 := by
    rcases h2709 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p486 := by
    rcases h2714 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p487 := by
    rcases h2719 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p488 := by
    rcases h2724 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2604 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24342 (p477 p481 p484 p489 p490 p491 p492 p493 : Prop)
    (h24341 : p491 ∨ p477 ∨ p481)
    (h2702 : p484 ∨ p489)
    (h2703 : p484 ∨ p490)
    (h2705 : p484 ∨ p492)
    (h2706 : p484 ∨ p493)
    (h2629 : p477 ∨ p481 ∨ (¬ p489) ∨ (¬ p490) ∨ (¬ p491) ∨ (¬ p492) ∨ (¬ p493)) : p484 ∨ p477 ∨ p481 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p484) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p477) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p481) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p491 := by
    rcases h24341 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p489 := by
    rcases h2702 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p490 := by
    rcases h2703 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p492 := by
    rcases h2705 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p493 := by
    rcases h2706 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2629 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24343 (p477 p481 p485 p489 p490 p491 p492 p493 : Prop)
    (h24341 : p491 ∨ p477 ∨ p481)
    (h2707 : p485 ∨ p489)
    (h2708 : p485 ∨ p490)
    (h2710 : p485 ∨ p492)
    (h2711 : p485 ∨ p493)
    (h2629 : p477 ∨ p481 ∨ (¬ p489) ∨ (¬ p490) ∨ (¬ p491) ∨ (¬ p492) ∨ (¬ p493)) : p485 ∨ p477 ∨ p481 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p485) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p477) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p481) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p491 := by
    rcases h24341 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p489 := by
    rcases h2707 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p490 := by
    rcases h2708 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p492 := by
    rcases h2710 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p493 := by
    rcases h2711 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2629 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24344 (p477 p481 p486 p489 p490 p491 p492 p493 : Prop)
    (h24341 : p491 ∨ p477 ∨ p481)
    (h2712 : p486 ∨ p489)
    (h2713 : p486 ∨ p490)
    (h2715 : p486 ∨ p492)
    (h2716 : p486 ∨ p493)
    (h2629 : p477 ∨ p481 ∨ (¬ p489) ∨ (¬ p490) ∨ (¬ p491) ∨ (¬ p492) ∨ (¬ p493)) : p486 ∨ p477 ∨ p481 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p486) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p477) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p481) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p491 := by
    rcases h24341 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p489 := by
    rcases h2712 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p490 := by
    rcases h2713 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p492 := by
    rcases h2715 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p493 := by
    rcases h2716 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2629 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24345 (p477 p481 p487 p489 p490 p491 p492 p493 : Prop)
    (h24341 : p491 ∨ p477 ∨ p481)
    (h2717 : p487 ∨ p489)
    (h2718 : p487 ∨ p490)
    (h2720 : p487 ∨ p492)
    (h2721 : p487 ∨ p493)
    (h2629 : p477 ∨ p481 ∨ (¬ p489) ∨ (¬ p490) ∨ (¬ p491) ∨ (¬ p492) ∨ (¬ p493)) : p487 ∨ p477 ∨ p481 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p487) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p477) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p481) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p491 := by
    rcases h24341 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p489 := by
    rcases h2717 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p490 := by
    rcases h2718 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p492 := by
    rcases h2720 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p493 := by
    rcases h2721 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2629 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24346 (p477 p481 p484 p485 p486 p487 p488 p489 p490 p491 p492 p493 : Prop)
    (h24341 : p491 ∨ p477 ∨ p481)
    (h24342 : p484 ∨ p477 ∨ p481)
    (h24343 : p485 ∨ p477 ∨ p481)
    (h24344 : p486 ∨ p477 ∨ p481)
    (h24345 : p487 ∨ p477 ∨ p481)
    (h2604 : p477 ∨ p481 ∨ (¬ p484) ∨ (¬ p485) ∨ (¬ p486) ∨ (¬ p487) ∨ (¬ p488))
    (h2722 : p488 ∨ p489)
    (h2723 : p488 ∨ p490)
    (h2725 : p488 ∨ p492)
    (h2726 : p488 ∨ p493)
    (h2629 : p477 ∨ p481 ∨ (¬ p489) ∨ (¬ p490) ∨ (¬ p491) ∨ (¬ p492) ∨ (¬ p493)) : p477 ∨ p481 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p477) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p481) := fun hu => hn (Or.inr hu)
  have u2 : p491 := by
    rcases h24341 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p484 := by
    rcases h24342 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p485 := by
    rcases h24343 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p486 := by
    rcases h24344 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p487 := by
    rcases h24345 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p488) := by
    rcases h2604 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u0 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p489 := by
    rcases h2722 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p490 := by
    rcases h2723 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p492 := by
    rcases h2725 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p493 := by
    rcases h2726 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h2629 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step24347 (p2 p481 p488 p489 p490 p491 p492 p493 : Prop)
    (h2722 : p488 ∨ p489)
    (h2723 : p488 ∨ p490)
    (h2725 : p488 ∨ p492)
    (h2726 : p488 ∨ p493)
    (h2639 : p2 ∨ p481 ∨ (¬ p489) ∨ (¬ p490) ∨ (¬ p491) ∨ (¬ p492) ∨ (¬ p493)) : p488 ∨ (¬ p491) ∨ p2 ∨ p481 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p488) := fun hu => hn (Or.inl hu)
  have u1 : p491 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p481) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p489 := by
    rcases h2722 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p490 := by
    rcases h2723 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p492 := by
    rcases h2725 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p493 := by
    rcases h2726 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2639 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24348 (p2 p481 p484 p485 p486 p487 p488 p492 : Prop)
    (h2705 : p484 ∨ p492)
    (h2710 : p485 ∨ p492)
    (h2715 : p486 ∨ p492)
    (h2720 : p487 ∨ p492)
    (h2614 : p2 ∨ p481 ∨ (¬ p484) ∨ (¬ p485) ∨ (¬ p486) ∨ (¬ p487) ∨ (¬ p488)) : p492 ∨ (¬ p488) ∨ p2 ∨ p481 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p492) := fun hu => hn (Or.inl hu)
  have u1 : p488 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p481) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p484 := by
    rcases h2705 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p485 := by
    rcases h2710 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p486 := by
    rcases h2715 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p487 := by
    rcases h2720 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2614 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24349 (p2 p481 p484 p485 p486 p487 p488 p493 : Prop)
    (h2706 : p484 ∨ p493)
    (h2711 : p485 ∨ p493)
    (h2716 : p486 ∨ p493)
    (h2721 : p487 ∨ p493)
    (h2614 : p2 ∨ p481 ∨ (¬ p484) ∨ (¬ p485) ∨ (¬ p486) ∨ (¬ p487) ∨ (¬ p488)) : p493 ∨ (¬ p488) ∨ p2 ∨ p481 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p493) := fun hu => hn (Or.inl hu)
  have u1 : p488 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p481) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p484 := by
    rcases h2706 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p485 := by
    rcases h2711 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p486 := by
    rcases h2716 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p487 := by
    rcases h2721 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2614 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24350 (p2 p481 p484 p485 p486 p487 p488 p489 : Prop)
    (h2702 : p484 ∨ p489)
    (h2707 : p485 ∨ p489)
    (h2712 : p486 ∨ p489)
    (h2717 : p487 ∨ p489)
    (h2614 : p2 ∨ p481 ∨ (¬ p484) ∨ (¬ p485) ∨ (¬ p486) ∨ (¬ p487) ∨ (¬ p488)) : p489 ∨ (¬ p488) ∨ p2 ∨ p481 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p489) := fun hu => hn (Or.inl hu)
  have u1 : p488 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p481) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p484 := by
    rcases h2702 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p485 := by
    rcases h2707 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p486 := by
    rcases h2712 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p487 := by
    rcases h2717 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2614 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24351 (p2 p481 p484 p485 p486 p487 p488 p489 p490 p491 p492 p493 : Prop)
    (h24347 : p488 ∨ (¬ p491) ∨ p2 ∨ p481)
    (h24348 : p492 ∨ (¬ p488) ∨ p2 ∨ p481)
    (h24349 : p493 ∨ (¬ p488) ∨ p2 ∨ p481)
    (h24350 : p489 ∨ (¬ p488) ∨ p2 ∨ p481)
    (h2639 : p2 ∨ p481 ∨ (¬ p489) ∨ (¬ p490) ∨ (¬ p491) ∨ (¬ p492) ∨ (¬ p493))
    (h2703 : p484 ∨ p490)
    (h2708 : p485 ∨ p490)
    (h2713 : p486 ∨ p490)
    (h2718 : p487 ∨ p490)
    (h2614 : p2 ∨ p481 ∨ (¬ p484) ∨ (¬ p485) ∨ (¬ p486) ∨ (¬ p487) ∨ (¬ p488)) : (¬ p491) ∨ p481 ∨ p2 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p491 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p481) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p2) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p488 := by
    rcases h24347 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u2 q2)
    · exact False.elim (u1 q3)
  have u4 : p492 := by
    rcases h24348 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u2 q2)
    · exact False.elim (u1 q3)
  have u5 : p493 := by
    rcases h24349 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u2 q2)
    · exact False.elim (u1 q3)
  have u6 : p489 := by
    rcases h24350 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u2 q2)
    · exact False.elim (u1 q3)
  have u7 : (¬ p490) := by
    rcases h2639 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u6)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u5)
  have u8 : p484 := by
    rcases h2703 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p485 := by
    rcases h2708 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p486 := by
    rcases h2713 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p487 := by
    rcases h2718 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h2614 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u3)

theorem step24352 (p2 p481 p484 p485 p486 p487 p488 p491 : Prop)
    (h24351 : (¬ p491) ∨ p481 ∨ p2)
    (h2704 : p484 ∨ p491)
    (h2709 : p485 ∨ p491)
    (h2714 : p486 ∨ p491)
    (h2719 : p487 ∨ p491)
    (h2724 : p488 ∨ p491)
    (h2614 : p2 ∨ p481 ∨ (¬ p484) ∨ (¬ p485) ∨ (¬ p486) ∨ (¬ p487) ∨ (¬ p488)) : p481 ∨ p2 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p481) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p2) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p491) := by
    rcases h24351 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p484 := by
    rcases h2704 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : p485 := by
    rcases h2709 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p486 := by
    rcases h2714 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p487 := by
    rcases h2719 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p488 := by
    rcases h2724 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h2614 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24353 (p2 p15 p18 p19 p22 p25 p71 p194 p224 p225 p234 p256 p288 p304 p344 p382 p419 p481 p495 p545 p657 p880 p884 p1099 p1187 : Prop)
    (h16985 : (¬ p256) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p657))
    (h20814 : p224 ∨ p657)
    (h5072 : (¬ p15) ∨ (¬ p25) ∨ (¬ p495))
    (h8753 : (¬ p15) ∨ (¬ p884) ∨ (¬ p1099))
    (h23949 : p25 ∨ p18)
    (h23127 : p884 ∨ p880)
    (h4 : (¬ p18) ∨ (¬ p19))
    (h16335 : (¬ p15) ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p880) ∨ (¬ p1099))
    (h23396 : p22 ∨ p19)
    (h23583 : p545 ∨ p225)
    (h24327 : (¬ p234) ∨ (¬ p15) ∨ (¬ p495))
    (h21531 : p1187 ∨ p234)
    (h24328 : p419 ∨ (¬ p545) ∨ (¬ p382) ∨ (¬ p194) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p256))
    (h18058 : (¬ p22) ∨ (¬ p71) ∨ (¬ p481) ∨ (¬ p495) ∨ (¬ p1187))
    (h24120 : p304 ∨ (¬ p419) ∨ (¬ p2))
    (h24352 : p481 ∨ p2) : (¬ p15) ∨ (¬ p382) ∨ (¬ p495) ∨ (¬ p194) ∨ (¬ p288) ∨ (¬ p71) ∨ (¬ p344) ∨ p304 ∨ (¬ p256) ∨ (¬ p1099) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p304) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p657) := by
    rcases h16985 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u8)
    · exact False.elim (q1 u4)
    · exact False.elim (q2 u6)
    · exact q3
  have u11 : p224 := by
    rcases h20814 with q0 | q1
    · exact q0
    · exact False.elim (u10 q1)
  have u12 : (¬ p25) := by
    rcases h5072 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (q2 u2)
  have u13 : (¬ p884) := by
    rcases h8753 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (q2 u9)
  have u14 : p18 := by
    rcases h23949 with q0 | q1
    · exact False.elim (u12 q0)
    · exact q1
  have u15 : p880 := by
    rcases h23127 with q0 | q1
    · exact False.elim (u13 q0)
    · exact q1
  have u16 : (¬ p19) := by
    rcases h4 with q0 | q1
    · exact False.elim (q0 u14)
    · exact q1
  have u17 : (¬ p225) := by
    rcases h16335 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u0)
    · exact False.elim (q1 u11)
    · exact q2
    · exact False.elim (q3 u15)
    · exact False.elim (q4 u9)
  have u18 : p22 := by
    rcases h23396 with q0 | q1
    · exact q0
    · exact False.elim (u16 q1)
  have u19 : p545 := by
    rcases h23583 with q0 | q1
    · exact q0
    · exact False.elim (u17 q1)
  have u20 : (¬ p234) := by
    rcases h24327 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u2)
  have u21 : p1187 := by
    rcases h21531 with q0 | q1
    · exact q0
    · exact False.elim (u20 q1)
  have u22 : p419 := by
    rcases h24328 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact q0
    · exact False.elim (q1 u19)
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u3)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u6)
    · exact False.elim (q6 u8)
  have u23 : (¬ p481) := by
    rcases h18058 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u18)
    · exact False.elim (q1 u5)
    · exact q2
    · exact False.elim (q3 u2)
    · exact False.elim (q4 u21)
  have u24 : (¬ p2) := by
    rcases h24120 with q0 | q1 | q2
    · exact False.elim (u7 q0)
    · exact False.elim (q1 u22)
    · exact q2
  rcases h24352 with q0 | q1
  · exact False.elim (u23 q0)
  · exact False.elim (u24 q1)

theorem step24356 (p18 p19 p25 p44 p50 p69 p101 p102 p124 p134 p136 p142 p258 p330 p421 p595 p1192 : Prop)
    (h22840 : p19 ∨ p18)
    (h17321 : (¬ p19) ∨ p330)
    (h23949 : p25 ∨ p18)
    (h21927 : p136 ∨ p142)
    (h22176 : p142 ∨ p134)
    (h19861 : (¬ p44) ∨ (¬ p69) ∨ (¬ p134) ∨ (¬ p330) ∨ (¬ p595) ∨ (¬ p1192))
    (h22877 : p50 ∨ p44)
    (h16817 : (¬ p19) ∨ (¬ p50) ∨ (¬ p102) ∨ (¬ p136) ∨ (¬ p258))
    (h16814 : (¬ p25) ∨ (¬ p50) ∨ (¬ p101) ∨ (¬ p124) ∨ (¬ p134) ∨ (¬ p421))
    (h21623 : p101 ∨ p102) : p142 ∨ (¬ p595) ∨ (¬ p421) ∨ (¬ p1192) ∨ (¬ p69) ∨ p18 ∨ (¬ p258) ∨ (¬ p124) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p142) := fun hu => hn (Or.inl hu)
  have u1 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p19 := by
    rcases h22840 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u9 : p330 := by
    rcases h17321 with q0 | q1
    · exact False.elim (q0 u8)
    · exact q1
  have u10 : p25 := by
    rcases h23949 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u11 : p136 := by
    rcases h21927 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u12 : p134 := by
    rcases h22176 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u13 : (¬ p44) := by
    rcases h19861 with q0 | q1 | q2 | q3 | q4 | q5
    · exact q0
    · exact False.elim (q1 u4)
    · exact False.elim (q2 u12)
    · exact False.elim (q3 u9)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u3)
  have u14 : p50 := by
    rcases h22877 with q0 | q1
    · exact q0
    · exact False.elim (u13 q1)
  have u15 : (¬ p102) := by
    rcases h16817 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u8)
    · exact False.elim (q1 u14)
    · exact q2
    · exact False.elim (q3 u11)
    · exact False.elim (q4 u6)
  have u16 : (¬ p101) := by
    rcases h16814 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u10)
    · exact False.elim (q1 u14)
    · exact q2
    · exact False.elim (q3 u7)
    · exact False.elim (q4 u12)
    · exact False.elim (q5 u2)
  rcases h21623 with q0 | q1
  · exact False.elim (u16 q0)
  · exact False.elim (u15 q1)

theorem step24358 (p1349 p1354 p1356 p1357 p1358 p1359 p1360 p1363 : Prop)
    (h8200 : p1356 ∨ p1363)
    (h8205 : p1357 ∨ p1363)
    (h8210 : p1358 ∨ p1363)
    (h8215 : p1359 ∨ p1363)
    (h8220 : p1360 ∨ p1363)
    (h8111 : p1349 ∨ p1354 ∨ (¬ p1356) ∨ (¬ p1357) ∨ (¬ p1358) ∨ (¬ p1359) ∨ (¬ p1360)) : p1363 ∨ p1354 ∨ p1349 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1363) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1354) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1349) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1356 := by
    rcases h8200 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1357 := by
    rcases h8205 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1358 := by
    rcases h8210 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1359 := by
    rcases h8215 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1360 := by
    rcases h8220 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8111 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24359 (p1349 p1354 p1356 p1361 p1362 p1363 p1364 p1365 : Prop)
    (h24358 : p1363 ∨ p1354 ∨ p1349)
    (h8198 : p1356 ∨ p1361)
    (h8199 : p1356 ∨ p1362)
    (h8201 : p1356 ∨ p1364)
    (h8202 : p1356 ∨ p1365)
    (h8136 : p1349 ∨ p1354 ∨ (¬ p1361) ∨ (¬ p1362) ∨ (¬ p1363) ∨ (¬ p1364) ∨ (¬ p1365)) : p1356 ∨ p1354 ∨ p1349 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1356) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1354) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1349) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1363 := by
    rcases h24358 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1361 := by
    rcases h8198 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1362 := by
    rcases h8199 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1364 := by
    rcases h8201 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1365 := by
    rcases h8202 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8136 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24360 (p1349 p1354 p1357 p1361 p1362 p1363 p1364 p1365 : Prop)
    (h24358 : p1363 ∨ p1354 ∨ p1349)
    (h8203 : p1357 ∨ p1361)
    (h8204 : p1357 ∨ p1362)
    (h8206 : p1357 ∨ p1364)
    (h8207 : p1357 ∨ p1365)
    (h8136 : p1349 ∨ p1354 ∨ (¬ p1361) ∨ (¬ p1362) ∨ (¬ p1363) ∨ (¬ p1364) ∨ (¬ p1365)) : p1357 ∨ p1354 ∨ p1349 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1357) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1354) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1349) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1363 := by
    rcases h24358 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1361 := by
    rcases h8203 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1362 := by
    rcases h8204 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1364 := by
    rcases h8206 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1365 := by
    rcases h8207 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8136 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24361 (p1349 p1354 p1358 p1361 p1362 p1363 p1364 p1365 : Prop)
    (h24358 : p1363 ∨ p1354 ∨ p1349)
    (h8208 : p1358 ∨ p1361)
    (h8209 : p1358 ∨ p1362)
    (h8211 : p1358 ∨ p1364)
    (h8212 : p1358 ∨ p1365)
    (h8136 : p1349 ∨ p1354 ∨ (¬ p1361) ∨ (¬ p1362) ∨ (¬ p1363) ∨ (¬ p1364) ∨ (¬ p1365)) : p1358 ∨ p1354 ∨ p1349 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1358) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1354) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1349) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1363 := by
    rcases h24358 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1361 := by
    rcases h8208 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1362 := by
    rcases h8209 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1364 := by
    rcases h8211 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1365 := by
    rcases h8212 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8136 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24362 (p1349 p1354 p1359 p1361 p1362 p1363 p1364 p1365 : Prop)
    (h24358 : p1363 ∨ p1354 ∨ p1349)
    (h8213 : p1359 ∨ p1361)
    (h8214 : p1359 ∨ p1362)
    (h8216 : p1359 ∨ p1364)
    (h8217 : p1359 ∨ p1365)
    (h8136 : p1349 ∨ p1354 ∨ (¬ p1361) ∨ (¬ p1362) ∨ (¬ p1363) ∨ (¬ p1364) ∨ (¬ p1365)) : p1359 ∨ p1354 ∨ p1349 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1359) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1354) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1349) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1363 := by
    rcases h24358 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1361 := by
    rcases h8213 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1362 := by
    rcases h8214 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1364 := by
    rcases h8216 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1365 := by
    rcases h8217 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8136 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24363 (p1349 p1354 p1356 p1357 p1358 p1359 p1360 p1361 p1362 p1363 p1364 p1365 : Prop)
    (h24358 : p1363 ∨ p1354 ∨ p1349)
    (h24359 : p1356 ∨ p1354 ∨ p1349)
    (h24360 : p1357 ∨ p1354 ∨ p1349)
    (h24361 : p1358 ∨ p1354 ∨ p1349)
    (h24362 : p1359 ∨ p1354 ∨ p1349)
    (h8111 : p1349 ∨ p1354 ∨ (¬ p1356) ∨ (¬ p1357) ∨ (¬ p1358) ∨ (¬ p1359) ∨ (¬ p1360))
    (h8218 : p1360 ∨ p1361)
    (h8219 : p1360 ∨ p1362)
    (h8221 : p1360 ∨ p1364)
    (h8222 : p1360 ∨ p1365)
    (h8136 : p1349 ∨ p1354 ∨ (¬ p1361) ∨ (¬ p1362) ∨ (¬ p1363) ∨ (¬ p1364) ∨ (¬ p1365)) : p1354 ∨ p1349 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1354) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1349) := fun hu => hn (Or.inr hu)
  have u2 : p1363 := by
    rcases h24358 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1356 := by
    rcases h24359 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1357 := by
    rcases h24360 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1358 := by
    rcases h24361 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p1359 := by
    rcases h24362 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p1360) := by
    rcases h8111 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p1361 := by
    rcases h8218 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p1362 := by
    rcases h8219 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p1364 := by
    rcases h8221 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p1365 := by
    rcases h8222 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h8136 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step24364 (p187 p193 p196 p197 p198 p199 p200 p205 : Prop)
    (h1026 : p196 ∨ p205)
    (h1031 : p197 ∨ p205)
    (h1036 : p198 ∨ p205)
    (h1041 : p199 ∨ p205)
    (h1046 : p200 ∨ p205)
    (h929 : p187 ∨ p193 ∨ (¬ p196) ∨ (¬ p197) ∨ (¬ p198) ∨ (¬ p199) ∨ (¬ p200)) : p205 ∨ p187 ∨ p193 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p205) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p187) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p193) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p196 := by
    rcases h1026 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p197 := by
    rcases h1031 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p198 := by
    rcases h1036 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p199 := by
    rcases h1041 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p200 := by
    rcases h1046 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h929 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24365 (p187 p193 p196 p197 p198 p199 p200 p201 : Prop)
    (h1022 : p196 ∨ p201)
    (h1027 : p197 ∨ p201)
    (h1032 : p198 ∨ p201)
    (h1037 : p199 ∨ p201)
    (h1042 : p200 ∨ p201)
    (h929 : p187 ∨ p193 ∨ (¬ p196) ∨ (¬ p197) ∨ (¬ p198) ∨ (¬ p199) ∨ (¬ p200)) : p201 ∨ p187 ∨ p193 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p201) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p187) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p193) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p196 := by
    rcases h1022 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p197 := by
    rcases h1027 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p198 := by
    rcases h1032 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p199 := by
    rcases h1037 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p200 := by
    rcases h1042 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h929 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24366 (p187 p193 p196 p197 p198 p199 p200 p202 : Prop)
    (h1023 : p196 ∨ p202)
    (h1028 : p197 ∨ p202)
    (h1033 : p198 ∨ p202)
    (h1038 : p199 ∨ p202)
    (h1043 : p200 ∨ p202)
    (h929 : p187 ∨ p193 ∨ (¬ p196) ∨ (¬ p197) ∨ (¬ p198) ∨ (¬ p199) ∨ (¬ p200)) : p202 ∨ p187 ∨ p193 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p202) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p187) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p193) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p196 := by
    rcases h1023 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p197 := by
    rcases h1028 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p198 := by
    rcases h1033 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p199 := by
    rcases h1038 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p200 := by
    rcases h1043 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h929 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24367 (p187 p193 p196 p197 p198 p199 p200 p203 : Prop)
    (h1024 : p196 ∨ p203)
    (h1029 : p197 ∨ p203)
    (h1034 : p198 ∨ p203)
    (h1039 : p199 ∨ p203)
    (h1044 : p200 ∨ p203)
    (h929 : p187 ∨ p193 ∨ (¬ p196) ∨ (¬ p197) ∨ (¬ p198) ∨ (¬ p199) ∨ (¬ p200)) : p203 ∨ p187 ∨ p193 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p203) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p187) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p193) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p196 := by
    rcases h1024 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p197 := by
    rcases h1029 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p198 := by
    rcases h1034 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p199 := by
    rcases h1039 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p200 := by
    rcases h1044 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h929 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24368 (p187 p193 p196 p197 p198 p199 p200 p201 p202 p203 p204 p205 : Prop)
    (h954 : p187 ∨ p193 ∨ (¬ p201) ∨ (¬ p202) ∨ (¬ p203) ∨ (¬ p204) ∨ (¬ p205))
    (h1025 : p196 ∨ p204)
    (h1030 : p197 ∨ p204)
    (h1035 : p198 ∨ p204)
    (h1040 : p199 ∨ p204)
    (h1045 : p200 ∨ p204)
    (h929 : p187 ∨ p193 ∨ (¬ p196) ∨ (¬ p197) ∨ (¬ p198) ∨ (¬ p199) ∨ (¬ p200)) : (¬ p203) ∨ (¬ p202) ∨ (¬ p201) ∨ p193 ∨ p187 ∨ (¬ p205) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p203 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p202 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p201 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p193) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p187) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p205 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p204) := by
    rcases h954 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u4 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u2)
    · exact False.elim (q3 u1)
    · exact False.elim (q4 u0)
    · exact q5
    · exact False.elim (q6 u5)
  have u7 : p196 := by
    rcases h1025 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p197 := by
    rcases h1030 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p198 := by
    rcases h1035 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p199 := by
    rcases h1040 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p200 := by
    rcases h1045 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h929 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step24369 (p187 p193 p201 p202 p203 p205 : Prop)
    (h24364 : p205 ∨ p187 ∨ p193)
    (h24365 : p201 ∨ p187 ∨ p193)
    (h24366 : p202 ∨ p187 ∨ p193)
    (h24367 : p203 ∨ p187 ∨ p193)
    (h24368 : (¬ p203) ∨ (¬ p202) ∨ (¬ p201) ∨ p193 ∨ p187 ∨ (¬ p205)) : p187 ∨ p193 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p187) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p193) := fun hu => hn (Or.inr hu)
  have u2 : p205 := by
    rcases h24364 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p201 := by
    rcases h24365 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p202 := by
    rcases h24366 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p203 := by
    rcases h24367 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h24368 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (u1 q3)
  · exact False.elim (u0 q4)
  · exact False.elim (q5 u2)

theorem step24370 (p135 p136 p147 p149 p150 p151 p152 p153 : Prop)
    (h771 : p147 ∨ p149)
    (h772 : p147 ∨ p150)
    (h773 : p147 ∨ p151)
    (h774 : p147 ∨ p152)
    (h684 : p135 ∨ p136 ∨ (¬ p149) ∨ (¬ p150) ∨ (¬ p151) ∨ (¬ p152) ∨ (¬ p153)) : p147 ∨ (¬ p153) ∨ p135 ∨ p136 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p147) := fun hu => hn (Or.inl hu)
  have u1 : p153 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p135) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p136) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p149 := by
    rcases h771 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p150 := by
    rcases h772 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p151 := by
    rcases h773 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p152 := by
    rcases h774 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h684 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24371 (p134 p135 p144 p145 p146 p147 p148 p149 : Prop)
    (h756 : p144 ∨ p149)
    (h761 : p145 ∨ p149)
    (h766 : p146 ∨ p149)
    (h669 : p134 ∨ p135 ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p147) ∨ (¬ p148)) : p149 ∨ (¬ p148) ∨ (¬ p147) ∨ p135 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p149) := fun hu => hn (Or.inl hu)
  have u1 : p148 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p147 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p135) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p144 := by
    rcases h756 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p145 := by
    rcases h761 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p146 := by
    rcases h766 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h669 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u1)

theorem step24372 (p134 p135 p144 p145 p146 p147 p148 p150 : Prop)
    (h757 : p144 ∨ p150)
    (h762 : p145 ∨ p150)
    (h767 : p146 ∨ p150)
    (h669 : p134 ∨ p135 ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p147) ∨ (¬ p148)) : p150 ∨ (¬ p148) ∨ (¬ p147) ∨ p135 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p150) := fun hu => hn (Or.inl hu)
  have u1 : p148 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p147 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p135) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p144 := by
    rcases h757 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p145 := by
    rcases h762 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p146 := by
    rcases h767 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h669 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u1)

theorem step24373 (p134 p135 p144 p145 p146 p147 p148 p151 : Prop)
    (h758 : p144 ∨ p151)
    (h763 : p145 ∨ p151)
    (h768 : p146 ∨ p151)
    (h669 : p134 ∨ p135 ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p147) ∨ (¬ p148)) : p151 ∨ (¬ p148) ∨ (¬ p147) ∨ p135 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p151) := fun hu => hn (Or.inl hu)
  have u1 : p148 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p147 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p135) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p144 := by
    rcases h758 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p145 := by
    rcases h763 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p146 := by
    rcases h768 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h669 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u1)

theorem step24374 (p134 p135 p136 p144 p145 p146 p147 p148 p149 p150 p151 p152 p153 : Prop)
    (h24370 : p147 ∨ (¬ p153) ∨ p135 ∨ p136)
    (h24371 : p149 ∨ (¬ p148) ∨ (¬ p147) ∨ p135 ∨ p134)
    (h24372 : p150 ∨ (¬ p148) ∨ (¬ p147) ∨ p135 ∨ p134)
    (h24373 : p151 ∨ (¬ p148) ∨ (¬ p147) ∨ p135 ∨ p134)
    (h684 : p135 ∨ p136 ∨ (¬ p149) ∨ (¬ p150) ∨ (¬ p151) ∨ (¬ p152) ∨ (¬ p153))
    (h759 : p144 ∨ p152)
    (h764 : p145 ∨ p152)
    (h769 : p146 ∨ p152)
    (h669 : p134 ∨ p135 ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p147) ∨ (¬ p148)) : (¬ p148) ∨ (¬ p153) ∨ p135 ∨ p136 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p148 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p153 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p135) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p136) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p147 := by
    rcases h24370 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u1)
    · exact False.elim (u2 q2)
    · exact False.elim (u3 q3)
  have u6 : p149 := by
    rcases h24371 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u5)
    · exact False.elim (u2 q3)
    · exact False.elim (u4 q4)
  have u7 : p150 := by
    rcases h24372 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u5)
    · exact False.elim (u2 q3)
    · exact False.elim (u4 q4)
  have u8 : p151 := by
    rcases h24373 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u5)
    · exact False.elim (u2 q3)
    · exact False.elim (u4 q4)
  have u9 : (¬ p152) := by
    rcases h684 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u6)
    · exact False.elim (q3 u7)
    · exact False.elim (q4 u8)
    · exact q5
    · exact False.elim (q6 u1)
  have u10 : p144 := by
    rcases h759 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  have u11 : p145 := by
    rcases h764 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  have u12 : p146 := by
    rcases h769 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h669 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u12)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u0)

theorem step24375 (p134 p135 p136 p148 p149 p150 p151 p152 p153 : Prop)
    (h24374 : (¬ p148) ∨ (¬ p153) ∨ p135 ∨ p136 ∨ p134)
    (h776 : p148 ∨ p149)
    (h777 : p148 ∨ p150)
    (h778 : p148 ∨ p151)
    (h779 : p148 ∨ p152)
    (h684 : p135 ∨ p136 ∨ (¬ p149) ∨ (¬ p150) ∨ (¬ p151) ∨ (¬ p152) ∨ (¬ p153)) : (¬ p153) ∨ p134 ∨ p135 ∨ p136 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p153 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p134) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p135) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p136) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p148) := by
    rcases h24374 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u2 q2)
    · exact False.elim (u3 q3)
    · exact False.elim (u1 q4)
  have u5 : p149 := by
    rcases h776 with q0 | q1
    · exact False.elim (u4 q0)
    · exact q1
  have u6 : p150 := by
    rcases h777 with q0 | q1
    · exact False.elim (u4 q0)
    · exact q1
  have u7 : p151 := by
    rcases h778 with q0 | q1
    · exact False.elim (u4 q0)
    · exact q1
  have u8 : p152 := by
    rcases h779 with q0 | q1
    · exact False.elim (u4 q0)
    · exact q1
  rcases h684 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u0)

theorem step24376 (p134 p135 p136 p144 p145 p146 p147 p148 p153 : Prop)
    (h24375 : (¬ p153) ∨ p134 ∨ p135 ∨ p136)
    (h760 : p144 ∨ p153)
    (h765 : p145 ∨ p153)
    (h770 : p146 ∨ p153)
    (h775 : p147 ∨ p153)
    (h780 : p148 ∨ p153)
    (h669 : p134 ∨ p135 ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p147) ∨ (¬ p148)) : p134 ∨ p136 ∨ p135 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p134) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p136) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p135) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : (¬ p153) := by
    rcases h24375 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
    · exact False.elim (u1 q3)
  have u4 : p144 := by
    rcases h760 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u5 : p145 := by
    rcases h765 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p146 := by
    rcases h770 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p147 := by
    rcases h775 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p148 := by
    rcases h780 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h669 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u8)

theorem step24377 (p12 p17 p18 p27 p69 p85 p88 p104 p124 p134 p135 p136 p142 p163 p167 p189 p193 p256 p258 p266 p400 p404 p421 p595 p616 p619 p633 p665 p1192 p1226 p1333 p1387 p1394 : Prop)
    (h24295 : p27 ∨ p18)
    (h23606 : p88 ∨ p85)
    (h11322 : (¬ p404) ∨ (¬ p1226) ∨ (¬ p1333))
    (h24130 : p400 ∨ p404)
    (h10652 : (¬ p17) ∨ (¬ p256))
    (h21425 : p266 ∨ p17)
    (h10651 : (¬ p595) ∨ (¬ p616))
    (h10648 : (¬ p85) ∨ (¬ p595) ∨ (¬ p1387))
    (h24356 : p142 ∨ (¬ p595) ∨ (¬ p421) ∨ (¬ p1192) ∨ (¬ p69) ∨ p18 ∨ (¬ p258) ∨ (¬ p124))
    (h20790 : p619 ∨ p616)
    (h22650 : p1394 ∨ p1387)
    (h11275 : (¬ p134) ∨ (¬ p142))
    (h17273 : (¬ p27) ∨ (¬ p104) ∨ (¬ p142) ∨ (¬ p167) ∨ (¬ p633))
    (h21282 : p163 ∨ p167)
    (h16766 : (¬ p12) ∨ p88 ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p400) ∨ (¬ p619) ∨ (¬ p665) ∨ (¬ p1226) ∨ (¬ p1333) ∨ (¬ p1394))
    (h21262 : p189 ∨ p193)
    (h10655 : (¬ p136) ∨ p193 ∨ (¬ p256))
    (h17388 : (¬ p124) ∨ (¬ p135) ∨ (¬ p189) ∨ (¬ p258) ∨ (¬ p266))
    (h24376 : p134 ∨ p136 ∨ p135) : (¬ p595) ∨ (¬ p12) ∨ (¬ p1192) ∨ (¬ p69) ∨ (¬ p421) ∨ (¬ p633) ∨ p18 ∨ (¬ p104) ∨ p88 ∨ (¬ p665) ∨ (¬ p1226) ∨ (¬ p1333) ∨ (¬ p258) ∨ (¬ p124) ∨ (¬ p256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p88) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))))))
  have u15 : p27 := by
    rcases h24295 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u16 : p85 := by
    rcases h23606 with q0 | q1
    · exact False.elim (u8 q0)
    · exact q1
  have u17 : (¬ p404) := by
    rcases h11322 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u10)
    · exact False.elim (q2 u11)
  have u18 : p400 := by
    rcases h24130 with q0 | q1
    · exact q0
    · exact False.elim (u17 q1)
  have u19 : (¬ p17) := by
    rcases h10652 with q0 | q1
    · exact q0
    · exact False.elim (q1 u14)
  have u20 : p266 := by
    rcases h21425 with q0 | q1
    · exact q0
    · exact False.elim (u19 q1)
  have u21 : (¬ p616) := by
    rcases h10651 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u22 : (¬ p1387) := by
    rcases h10648 with q0 | q1 | q2
    · exact False.elim (q0 u16)
    · exact False.elim (q1 u0)
    · exact q2
  have u23 : p142 := by
    rcases h24356 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u2)
    · exact False.elim (q4 u3)
    · exact False.elim (u6 q5)
    · exact False.elim (q6 u12)
    · exact False.elim (q7 u13)
  have u24 : p619 := by
    rcases h20790 with q0 | q1
    · exact q0
    · exact False.elim (u21 q1)
  have u25 : p1394 := by
    rcases h22650 with q0 | q1
    · exact q0
    · exact False.elim (u22 q1)
  have u26 : (¬ p134) := by
    rcases h11275 with q0 | q1
    · exact q0
    · exact False.elim (q1 u23)
  have u27 : (¬ p167) := by
    rcases h17273 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u15)
    · exact False.elim (q1 u7)
    · exact False.elim (q2 u23)
    · exact q3
    · exact False.elim (q4 u5)
  have u28 : p163 := by
    rcases h21282 with q0 | q1
    · exact q0
    · exact False.elim (u27 q1)
  have u29 : (¬ p193) := by
    rcases h16766 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
    · exact False.elim (q0 u1)
    · exact False.elim (u8 q1)
    · exact False.elim (q2 u28)
    · exact q3
    · exact False.elim (q4 u18)
    · exact False.elim (q5 u24)
    · exact False.elim (q6 u9)
    · exact False.elim (q7 u10)
    · exact False.elim (q8 u11)
    · exact False.elim (q9 u25)
  have u30 : p189 := by
    rcases h21262 with q0 | q1
    · exact q0
    · exact False.elim (u29 q1)
  have u31 : (¬ p136) := by
    rcases h10655 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u29 q1)
    · exact False.elim (q2 u14)
  have u32 : (¬ p135) := by
    rcases h17388 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u13)
    · exact q1
    · exact False.elim (q2 u30)
    · exact False.elim (q3 u12)
    · exact False.elim (q4 u20)
  rcases h24376 with q0 | q1 | q2
  · exact False.elim (u26 q0)
  · exact False.elim (u31 q1)
  · exact False.elim (u32 q2)

theorem step24379 (p27 p101 p495 p499 p634 p639 p1096 : Prop)
    (h20942 : p495 ∨ p499)
    (h10764 : p499 ∨ (¬ p634) ∨ (¬ p1096))
    (h20491 : (¬ p27) ∨ (¬ p101) ∨ (¬ p495) ∨ (¬ p639) ∨ (¬ p1096))
    (h20840 : p639 ∨ p634) : (¬ p1096) ∨ p499 ∨ (¬ p27) ∨ (¬ p101) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p499) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p27 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p495 := by
    rcases h20942 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : (¬ p634) := by
    rcases h10764 with q0 | q1 | q2
    · exact False.elim (u1 q0)
    · exact q1
    · exact False.elim (q2 u0)
  have u6 : (¬ p639) := by
    rcases h20491 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u2)
    · exact False.elim (q1 u3)
    · exact False.elim (q2 u4)
    · exact q3
    · exact False.elim (q4 u0)
  rcases h20840 with q0 | q1
  · exact False.elim (u6 q0)
  · exact False.elim (u5 q1)

theorem step24381 (p636 p639 p647 p648 p649 p650 p651 p652 : Prop)
    (h3736 : p647 ∨ p648)
    (h3737 : p647 ∨ p649)
    (h3738 : p647 ∨ p650)
    (h3740 : p647 ∨ p652)
    (h3651 : p636 ∨ p639 ∨ (¬ p648) ∨ (¬ p649) ∨ (¬ p650) ∨ (¬ p651) ∨ (¬ p652)) : p647 ∨ (¬ p651) ∨ p636 ∨ p639 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p647) := fun hu => hn (Or.inl hu)
  have u1 : p651 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p636) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p639) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p648 := by
    rcases h3736 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p649 := by
    rcases h3737 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p650 := by
    rcases h3738 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p652 := by
    rcases h3740 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3651 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step24382 (p636 p639 p643 p648 p649 p650 p651 p652 : Prop)
    (h3716 : p643 ∨ p648)
    (h3717 : p643 ∨ p649)
    (h3718 : p643 ∨ p650)
    (h3720 : p643 ∨ p652)
    (h3651 : p636 ∨ p639 ∨ (¬ p648) ∨ (¬ p649) ∨ (¬ p650) ∨ (¬ p651) ∨ (¬ p652)) : p643 ∨ (¬ p651) ∨ p636 ∨ p639 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p643) := fun hu => hn (Or.inl hu)
  have u1 : p651 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p636) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p639) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p648 := by
    rcases h3716 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p649 := by
    rcases h3717 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p650 := by
    rcases h3718 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p652 := by
    rcases h3720 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3651 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step24383 (p636 p639 p644 p648 p649 p650 p651 p652 : Prop)
    (h3721 : p644 ∨ p648)
    (h3722 : p644 ∨ p649)
    (h3723 : p644 ∨ p650)
    (h3725 : p644 ∨ p652)
    (h3651 : p636 ∨ p639 ∨ (¬ p648) ∨ (¬ p649) ∨ (¬ p650) ∨ (¬ p651) ∨ (¬ p652)) : p644 ∨ (¬ p651) ∨ p636 ∨ p639 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p644) := fun hu => hn (Or.inl hu)
  have u1 : p651 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p636) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p639) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p648 := by
    rcases h3721 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p649 := by
    rcases h3722 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p650 := by
    rcases h3723 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p652 := by
    rcases h3725 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3651 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step24386 (p1000 p1001 p1009 p1010 p1011 p1012 p1013 p1014 : Prop)
    (h5958 : p1009 ∨ p1010)
    (h5959 : p1009 ∨ p1011)
    (h5961 : p1009 ∨ p1013)
    (h5962 : p1009 ∨ p1014)
    (h5883 : p1000 ∨ p1001 ∨ (¬ p1010) ∨ (¬ p1011) ∨ (¬ p1012) ∨ (¬ p1013) ∨ (¬ p1014)) : p1009 ∨ (¬ p1012) ∨ p1000 ∨ p1001 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1009) := fun hu => hn (Or.inl hu)
  have u1 : p1012 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1000) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1001) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1010 := by
    rcases h5958 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1011 := by
    rcases h5959 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1013 := by
    rcases h5961 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1014 := by
    rcases h5962 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5883 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24387 (p996 p1000 p1005 p1006 p1007 p1008 p1009 p1013 : Prop)
    (h5941 : p1005 ∨ p1013)
    (h5946 : p1006 ∨ p1013)
    (h5951 : p1007 ∨ p1013)
    (h5956 : p1008 ∨ p1013)
    (h5860 : p996 ∨ p1000 ∨ (¬ p1005) ∨ (¬ p1006) ∨ (¬ p1007) ∨ (¬ p1008) ∨ (¬ p1009)) : p1013 ∨ (¬ p1009) ∨ p1000 ∨ p996 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1013) := fun hu => hn (Or.inl hu)
  have u1 : p1009 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1000) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p996) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1005 := by
    rcases h5941 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1006 := by
    rcases h5946 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1007 := by
    rcases h5951 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1008 := by
    rcases h5956 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5860 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24388 (p996 p1000 p1005 p1006 p1007 p1008 p1009 p1014 : Prop)
    (h5942 : p1005 ∨ p1014)
    (h5947 : p1006 ∨ p1014)
    (h5952 : p1007 ∨ p1014)
    (h5957 : p1008 ∨ p1014)
    (h5860 : p996 ∨ p1000 ∨ (¬ p1005) ∨ (¬ p1006) ∨ (¬ p1007) ∨ (¬ p1008) ∨ (¬ p1009)) : p1014 ∨ (¬ p1009) ∨ p1000 ∨ p996 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1014) := fun hu => hn (Or.inl hu)
  have u1 : p1009 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1000) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p996) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1005 := by
    rcases h5942 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1006 := by
    rcases h5947 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1007 := by
    rcases h5952 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1008 := by
    rcases h5957 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5860 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24389 (p996 p1000 p1005 p1006 p1007 p1008 p1009 p1010 : Prop)
    (h5938 : p1005 ∨ p1010)
    (h5943 : p1006 ∨ p1010)
    (h5948 : p1007 ∨ p1010)
    (h5953 : p1008 ∨ p1010)
    (h5860 : p996 ∨ p1000 ∨ (¬ p1005) ∨ (¬ p1006) ∨ (¬ p1007) ∨ (¬ p1008) ∨ (¬ p1009)) : p1010 ∨ (¬ p1009) ∨ p1000 ∨ p996 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1010) := fun hu => hn (Or.inl hu)
  have u1 : p1009 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1000) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p996) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1005 := by
    rcases h5938 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1006 := by
    rcases h5943 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1007 := by
    rcases h5948 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1008 := by
    rcases h5953 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5860 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24390 (p996 p1000 p1001 p1005 p1006 p1007 p1008 p1009 p1010 p1011 p1012 p1013 p1014 : Prop)
    (h24386 : p1009 ∨ (¬ p1012) ∨ p1000 ∨ p1001)
    (h24387 : p1013 ∨ (¬ p1009) ∨ p1000 ∨ p996)
    (h24388 : p1014 ∨ (¬ p1009) ∨ p1000 ∨ p996)
    (h24389 : p1010 ∨ (¬ p1009) ∨ p1000 ∨ p996)
    (h5883 : p1000 ∨ p1001 ∨ (¬ p1010) ∨ (¬ p1011) ∨ (¬ p1012) ∨ (¬ p1013) ∨ (¬ p1014))
    (h5939 : p1005 ∨ p1011)
    (h5944 : p1006 ∨ p1011)
    (h5949 : p1007 ∨ p1011)
    (h5954 : p1008 ∨ p1011)
    (h5860 : p996 ∨ p1000 ∨ (¬ p1005) ∨ (¬ p1006) ∨ (¬ p1007) ∨ (¬ p1008) ∨ (¬ p1009)) : (¬ p1012) ∨ p1000 ∨ p1001 ∨ p996 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1012 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1000) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1001) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p996) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1009 := by
    rcases h24386 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u5 : p1013 := by
    rcases h24387 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u4)
    · exact False.elim (u1 q2)
    · exact False.elim (u3 q3)
  have u6 : p1014 := by
    rcases h24388 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u4)
    · exact False.elim (u1 q2)
    · exact False.elim (u3 q3)
  have u7 : p1010 := by
    rcases h24389 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u4)
    · exact False.elim (u1 q2)
    · exact False.elim (u3 q3)
  have u8 : (¬ p1011) := by
    rcases h5883 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u7)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u6)
  have u9 : p1005 := by
    rcases h5939 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u10 : p1006 := by
    rcases h5944 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u11 : p1007 := by
    rcases h5949 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u12 : p1008 := by
    rcases h5954 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h5860 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u12)
  · exact False.elim (q6 u4)

theorem step24391 (p996 p1000 p1001 p1005 p1006 p1007 p1008 p1009 p1012 : Prop)
    (h24390 : (¬ p1012) ∨ p1000 ∨ p1001 ∨ p996)
    (h5940 : p1005 ∨ p1012)
    (h5945 : p1006 ∨ p1012)
    (h5950 : p1007 ∨ p1012)
    (h5955 : p1008 ∨ p1012)
    (h5960 : p1009 ∨ p1012)
    (h5860 : p996 ∨ p1000 ∨ (¬ p1005) ∨ (¬ p1006) ∨ (¬ p1007) ∨ (¬ p1008) ∨ (¬ p1009)) : p1000 ∨ p1001 ∨ p996 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1000) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1001) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p996) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1012) := by
    rcases h24390 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u4 : p1005 := by
    rcases h5940 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u5 : p1006 := by
    rcases h5945 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p1007 := by
    rcases h5950 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p1008 := by
    rcases h5955 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p1009 := by
    rcases h5960 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h5860 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u8)

theorem step24393 (p419 p1001 p1005 p1006 p1007 p1008 p1009 p1012 : Prop)
    (h5940 : p1005 ∨ p1012)
    (h5945 : p1006 ∨ p1012)
    (h5950 : p1007 ∨ p1012)
    (h5955 : p1008 ∨ p1012)
    (h5960 : p1009 ∨ p1012)
    (h5848 : p419 ∨ p1001 ∨ (¬ p1005) ∨ (¬ p1006) ∨ (¬ p1007) ∨ (¬ p1008) ∨ (¬ p1009)) : p1012 ∨ p419 ∨ p1001 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1012) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p419) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1001) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1005 := by
    rcases h5940 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1006 := by
    rcases h5945 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1007 := by
    rcases h5950 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1008 := by
    rcases h5955 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1009 := by
    rcases h5960 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5848 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24396 (p3 p12 p105 p127 p556 p560 p1055 p1061 : Prop)
    (h20663 : p1061 ∨ p1055)
    (h13483 : (¬ p12) ∨ (¬ p560) ∨ p1061)
    (h16239 : (¬ p12) ∨ (¬ p105) ∨ (¬ p127) ∨ (¬ p556) ∨ (¬ p1055))
    (h23426 : p556 ∨ p560 ∨ p3) : p1061 ∨ (¬ p12) ∨ (¬ p127) ∨ (¬ p105) ∨ p3 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1061) := fun hu => hn (Or.inl hu)
  have u1 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1055 := by
    rcases h20663 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : (¬ p560) := by
    rcases h13483 with q0 | q1 | q2
    · exact False.elim (q0 u1)
    · exact q1
    · exact False.elim (u0 q2)
  have u7 : (¬ p556) := by
    rcases h16239 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u1)
    · exact False.elim (q1 u3)
    · exact False.elim (q2 u2)
    · exact q3
    · exact False.elim (q4 u5)
  rcases h23426 with q0 | q1 | q2
  · exact False.elim (u7 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (u4 q2)

theorem step24397 (p12 p105 p142 p165 p169 p557 p1061 p1115 p1116 : Prop)
    (h21858 : p1115 ∨ p1116)
    (h14625 : (¬ p12) ∨ (¬ p169) ∨ p1116)
    (h18766 : (¬ p105) ∨ (¬ p142) ∨ (¬ p165) ∨ (¬ p557) ∨ (¬ p1061) ∨ (¬ p1115))
    (h21921 : p165 ∨ p169) : p1116 ∨ (¬ p1061) ∨ (¬ p12) ∨ (¬ p142) ∨ (¬ p105) ∨ (¬ p557) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1116) := fun hu => hn (Or.inl hu)
  have u1 : p1061 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1115 := by
    rcases h21858 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : (¬ p169) := by
    rcases h14625 with q0 | q1 | q2
    · exact False.elim (q0 u2)
    · exact q1
    · exact False.elim (u0 q2)
  have u8 : (¬ p165) := by
    rcases h18766 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u4)
    · exact False.elim (q1 u3)
    · exact q2
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u6)
  rcases h21921 with q0 | q1
  · exact False.elim (u8 q0)
  · exact False.elim (u7 q1)

theorem step24398 (p105 p142 p163 p166 p170 p185 p193 : Prop)
    (h10852 : (¬ p170) ∨ (¬ p185) ∨ (¬ p193))
    (h19582 : (¬ p105) ∨ (¬ p142) ∨ (¬ p166) ∨ (¬ p185) ∨ (¬ p193))
    (h23527 : p166 ∨ p170 ∨ p163) : (¬ p185) ∨ (¬ p142) ∨ (¬ p105) ∨ p163 ∨ (¬ p193) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p170) := by
    rcases h10852 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u4)
  have u6 : (¬ p166) := by
    rcases h19582 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u2)
    · exact False.elim (q1 u1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
  rcases h23527 with q0 | q1 | q2
  · exact False.elim (u6 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (u3 q2)

theorem step24399 (p38 p67 p160 p423 p1035 p1140 p1141 p1159 p1163 p1167 p1171 p1172 p1173 p1174 p1175 p1176 p1177 p1178 p1179 p1180 p1226 : Prop)
    (h21650 : p1159 ∨ p1140)
    (h14347 : (¬ p38) ∨ p1141 ∨ (¬ p1159))
    (h21299 : p67 ∨ p38)
    (h20723 : p423 ∨ p1141)
    (h19277 : (¬ p67) ∨ (¬ p423) ∨ (¬ p1035) ∨ (¬ p1163) ∨ (¬ p1226))
    (h11185 : p160 ∨ (¬ p1035) ∨ (¬ p1167))
    (h24319 : p1179 ∨ p1163 ∨ p1140)
    (h24320 : p1171 ∨ p1163 ∨ p1140)
    (h24321 : p1172 ∨ p1163 ∨ p1140)
    (h24322 : p1173 ∨ p1163 ∨ p1140)
    (h24323 : p1174 ∨ p1163 ∨ p1140)
    (h6894 : p1163 ∨ p1167 ∨ (¬ p1171) ∨ (¬ p1172) ∨ (¬ p1173) ∨ (¬ p1174) ∨ (¬ p1175))
    (h7014 : p1175 ∨ p1176)
    (h7015 : p1175 ∨ p1177)
    (h7016 : p1175 ∨ p1178)
    (h7018 : p1175 ∨ p1180)
    (h6921 : p1140 ∨ p1163 ∨ (¬ p1176) ∨ (¬ p1177) ∨ (¬ p1178) ∨ (¬ p1179) ∨ (¬ p1180)) : (¬ p1035) ∨ (¬ p1226) ∨ p160 ∨ p1141 ∨ p1140 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p160) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1141) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1159 := by
    rcases h21650 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u6 : (¬ p38) := by
    rcases h14347 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u5)
  have u7 : p67 := by
    rcases h21299 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p423 := by
    rcases h20723 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : (¬ p1163) := by
    rcases h19277 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u7)
    · exact False.elim (q1 u8)
    · exact False.elim (q2 u0)
    · exact q3
    · exact False.elim (q4 u1)
  have u10 : (¬ p1167) := by
    rcases h11185 with q0 | q1 | q2
    · exact False.elim (u2 q0)
    · exact False.elim (q1 u0)
    · exact q2
  have u11 : p1179 := by
    rcases h24319 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u9 q1)
    · exact False.elim (u4 q2)
  have u12 : p1171 := by
    rcases h24320 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u9 q1)
    · exact False.elim (u4 q2)
  have u13 : p1172 := by
    rcases h24321 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u9 q1)
    · exact False.elim (u4 q2)
  have u14 : p1173 := by
    rcases h24322 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u9 q1)
    · exact False.elim (u4 q2)
  have u15 : p1174 := by
    rcases h24323 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u9 q1)
    · exact False.elim (u4 q2)
  have u16 : (¬ p1175) := by
    rcases h6894 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u9 q0)
    · exact False.elim (u10 q1)
    · exact False.elim (q2 u12)
    · exact False.elim (q3 u13)
    · exact False.elim (q4 u14)
    · exact False.elim (q5 u15)
    · exact q6
  have u17 : p1176 := by
    rcases h7014 with q0 | q1
    · exact False.elim (u16 q0)
    · exact q1
  have u18 : p1177 := by
    rcases h7015 with q0 | q1
    · exact False.elim (u16 q0)
    · exact q1
  have u19 : p1178 := by
    rcases h7016 with q0 | q1
    · exact False.elim (u16 q0)
    · exact q1
  have u20 : p1180 := by
    rcases h7018 with q0 | q1
    · exact False.elim (u16 q0)
    · exact q1
  rcases h6921 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u9 q1)
  · exact False.elim (q2 u17)
  · exact False.elim (q3 u18)
  · exact False.elim (q4 u19)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u20)

theorem step24400 (p979 p983 p986 p987 p988 p989 p990 p994 : Prop)
    (h5815 : p986 ∨ p994)
    (h5820 : p987 ∨ p994)
    (h5825 : p988 ∨ p994)
    (h5830 : p989 ∨ p994)
    (h5835 : p990 ∨ p994)
    (h5719 : p979 ∨ p983 ∨ (¬ p986) ∨ (¬ p987) ∨ (¬ p988) ∨ (¬ p989) ∨ (¬ p990)) : p994 ∨ p979 ∨ p983 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p994) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p979) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p983) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p986 := by
    rcases h5815 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p987 := by
    rcases h5820 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p988 := by
    rcases h5825 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p989 := by
    rcases h5830 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p990 := by
    rcases h5835 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5719 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24401 (p979 p983 p986 p987 p988 p989 p990 p995 : Prop)
    (h5816 : p986 ∨ p995)
    (h5821 : p987 ∨ p995)
    (h5826 : p988 ∨ p995)
    (h5831 : p989 ∨ p995)
    (h5836 : p990 ∨ p995)
    (h5719 : p979 ∨ p983 ∨ (¬ p986) ∨ (¬ p987) ∨ (¬ p988) ∨ (¬ p989) ∨ (¬ p990)) : p995 ∨ p979 ∨ p983 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p995) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p979) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p983) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p986 := by
    rcases h5816 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p987 := by
    rcases h5821 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p988 := by
    rcases h5826 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p989 := by
    rcases h5831 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p990 := by
    rcases h5836 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5719 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24402 (p979 p983 p986 p987 p988 p989 p990 p991 : Prop)
    (h5812 : p986 ∨ p991)
    (h5817 : p987 ∨ p991)
    (h5822 : p988 ∨ p991)
    (h5827 : p989 ∨ p991)
    (h5832 : p990 ∨ p991)
    (h5719 : p979 ∨ p983 ∨ (¬ p986) ∨ (¬ p987) ∨ (¬ p988) ∨ (¬ p989) ∨ (¬ p990)) : p991 ∨ p979 ∨ p983 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p991) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p979) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p983) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p986 := by
    rcases h5812 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p987 := by
    rcases h5817 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p988 := by
    rcases h5822 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p989 := by
    rcases h5827 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p990 := by
    rcases h5832 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5719 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24403 (p979 p983 p986 p987 p988 p989 p990 p992 : Prop)
    (h5813 : p986 ∨ p992)
    (h5818 : p987 ∨ p992)
    (h5823 : p988 ∨ p992)
    (h5828 : p989 ∨ p992)
    (h5833 : p990 ∨ p992)
    (h5719 : p979 ∨ p983 ∨ (¬ p986) ∨ (¬ p987) ∨ (¬ p988) ∨ (¬ p989) ∨ (¬ p990)) : p992 ∨ p979 ∨ p983 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p992) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p979) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p983) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p986 := by
    rcases h5813 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p987 := by
    rcases h5818 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p988 := by
    rcases h5823 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p989 := by
    rcases h5828 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p990 := by
    rcases h5833 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5719 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24404 (p979 p983 p986 p987 p988 p989 p990 p991 p992 p993 p994 p995 : Prop)
    (h5744 : p979 ∨ p983 ∨ (¬ p991) ∨ (¬ p992) ∨ (¬ p993) ∨ (¬ p994) ∨ (¬ p995))
    (h5814 : p986 ∨ p993)
    (h5819 : p987 ∨ p993)
    (h5824 : p988 ∨ p993)
    (h5829 : p989 ∨ p993)
    (h5834 : p990 ∨ p993)
    (h5719 : p979 ∨ p983 ∨ (¬ p986) ∨ (¬ p987) ∨ (¬ p988) ∨ (¬ p989) ∨ (¬ p990)) : (¬ p992) ∨ (¬ p991) ∨ p983 ∨ p979 ∨ (¬ p994) ∨ (¬ p995) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p992 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p991 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p983) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p979) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p994 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p995 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p993) := by
    rcases h5744 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u0)
    · exact q4
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u5)
  have u7 : p986 := by
    rcases h5814 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p987 := by
    rcases h5819 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p988 := by
    rcases h5824 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p989 := by
    rcases h5829 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p990 := by
    rcases h5834 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h5719 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step24405 (p979 p983 p991 p992 p994 p995 : Prop)
    (h24400 : p994 ∨ p979 ∨ p983)
    (h24401 : p995 ∨ p979 ∨ p983)
    (h24402 : p991 ∨ p979 ∨ p983)
    (h24403 : p992 ∨ p979 ∨ p983)
    (h24404 : (¬ p992) ∨ (¬ p991) ∨ p983 ∨ p979 ∨ (¬ p994) ∨ (¬ p995)) : p979 ∨ p983 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p979) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p983) := fun hu => hn (Or.inr hu)
  have u2 : p994 := by
    rcases h24400 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p995 := by
    rcases h24401 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p991 := by
    rcases h24402 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p992 := by
    rcases h24403 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h24404 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step24406 (p576 p582 p586 p589 p590 p591 p592 p593 : Prop)
    (h3348 : p586 ∨ p589)
    (h3349 : p586 ∨ p590)
    (h3350 : p586 ∨ p591)
    (h3351 : p586 ∨ p592)
    (h3352 : p586 ∨ p593)
    (h3276 : p576 ∨ p582 ∨ (¬ p589) ∨ (¬ p590) ∨ (¬ p591) ∨ (¬ p592) ∨ (¬ p593)) : p586 ∨ p582 ∨ p576 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p586) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p582) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p576) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p589 := by
    rcases h3348 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p590 := by
    rcases h3349 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p591 := by
    rcases h3350 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p592 := by
    rcases h3351 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p593 := by
    rcases h3352 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3276 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24407 (p576 p582 p584 p585 p586 p587 p588 p592 : Prop)
    (h24406 : p586 ∨ p582 ∨ p576)
    (h3341 : p584 ∨ p592)
    (h3346 : p585 ∨ p592)
    (h3356 : p587 ∨ p592)
    (h3361 : p588 ∨ p592)
    (h3251 : p576 ∨ p582 ∨ (¬ p584) ∨ (¬ p585) ∨ (¬ p586) ∨ (¬ p587) ∨ (¬ p588)) : p592 ∨ p582 ∨ p576 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p592) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p582) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p576) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p586 := by
    rcases h24406 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p584 := by
    rcases h3341 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p585 := by
    rcases h3346 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p587 := by
    rcases h3356 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p588 := by
    rcases h3361 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3251 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24408 (p576 p582 p584 p585 p586 p587 p588 p591 : Prop)
    (h24406 : p586 ∨ p582 ∨ p576)
    (h3340 : p584 ∨ p591)
    (h3345 : p585 ∨ p591)
    (h3355 : p587 ∨ p591)
    (h3360 : p588 ∨ p591)
    (h3251 : p576 ∨ p582 ∨ (¬ p584) ∨ (¬ p585) ∨ (¬ p586) ∨ (¬ p587) ∨ (¬ p588)) : p591 ∨ p582 ∨ p576 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p591) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p582) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p576) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p586 := by
    rcases h24406 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p584 := by
    rcases h3340 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p585 := by
    rcases h3345 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p587 := by
    rcases h3355 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p588 := by
    rcases h3360 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3251 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24409 (p576 p582 p584 p585 p586 p587 p588 p593 : Prop)
    (h24406 : p586 ∨ p582 ∨ p576)
    (h3342 : p584 ∨ p593)
    (h3347 : p585 ∨ p593)
    (h3357 : p587 ∨ p593)
    (h3362 : p588 ∨ p593)
    (h3251 : p576 ∨ p582 ∨ (¬ p584) ∨ (¬ p585) ∨ (¬ p586) ∨ (¬ p587) ∨ (¬ p588)) : p593 ∨ p582 ∨ p576 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p593) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p582) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p576) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p586 := by
    rcases h24406 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p584 := by
    rcases h3342 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p585 := by
    rcases h3347 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p587 := by
    rcases h3357 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p588 := by
    rcases h3362 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3251 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24410 (p576 p582 p584 p585 p586 p587 p588 p589 : Prop)
    (h24406 : p586 ∨ p582 ∨ p576)
    (h3338 : p584 ∨ p589)
    (h3343 : p585 ∨ p589)
    (h3353 : p587 ∨ p589)
    (h3358 : p588 ∨ p589)
    (h3251 : p576 ∨ p582 ∨ (¬ p584) ∨ (¬ p585) ∨ (¬ p586) ∨ (¬ p587) ∨ (¬ p588)) : p589 ∨ p582 ∨ p576 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p589) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p582) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p576) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p586 := by
    rcases h24406 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p584 := by
    rcases h3338 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p585 := by
    rcases h3343 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p587 := by
    rcases h3353 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p588 := by
    rcases h3358 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3251 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24411 (p576 p582 p584 p585 p586 p587 p588 p589 p590 p591 p592 p593 : Prop)
    (h24406 : p586 ∨ p582 ∨ p576)
    (h24407 : p592 ∨ p582 ∨ p576)
    (h24408 : p591 ∨ p582 ∨ p576)
    (h24409 : p593 ∨ p582 ∨ p576)
    (h24410 : p589 ∨ p582 ∨ p576)
    (h3276 : p576 ∨ p582 ∨ (¬ p589) ∨ (¬ p590) ∨ (¬ p591) ∨ (¬ p592) ∨ (¬ p593))
    (h3339 : p584 ∨ p590)
    (h3344 : p585 ∨ p590)
    (h3354 : p587 ∨ p590)
    (h3359 : p588 ∨ p590)
    (h3251 : p576 ∨ p582 ∨ (¬ p584) ∨ (¬ p585) ∨ (¬ p586) ∨ (¬ p587) ∨ (¬ p588)) : p582 ∨ p576 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p582) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr hu)
  have u2 : p586 := by
    rcases h24406 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p592 := by
    rcases h24407 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p591 := by
    rcases h24408 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p593 := by
    rcases h24409 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p589 := by
    rcases h24410 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p590) := by
    rcases h3276 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u6)
    · exact q3
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u3)
    · exact False.elim (q6 u5)
  have u8 : p584 := by
    rcases h3339 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p585 := by
    rcases h3344 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p587 := by
    rcases h3354 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p588 := by
    rcases h3359 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h3251 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step24414 (p419 p1001 p1005 p1010 p1011 p1012 p1013 p1014 : Prop)
    (h24393 : p1012 ∨ p419 ∨ p1001)
    (h5938 : p1005 ∨ p1010)
    (h5939 : p1005 ∨ p1011)
    (h5941 : p1005 ∨ p1013)
    (h5942 : p1005 ∨ p1014)
    (h5873 : p419 ∨ p1001 ∨ (¬ p1010) ∨ (¬ p1011) ∨ (¬ p1012) ∨ (¬ p1013) ∨ (¬ p1014)) : p1005 ∨ p1001 ∨ p419 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1005) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1001) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p419) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1012 := by
    rcases h24393 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u2 q1)
    · exact False.elim (u1 q2)
  have u4 : p1010 := by
    rcases h5938 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1011 := by
    rcases h5939 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1013 := by
    rcases h5941 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1014 := by
    rcases h5942 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5873 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24415 (p419 p1001 p1006 p1010 p1011 p1012 p1013 p1014 : Prop)
    (h24393 : p1012 ∨ p419 ∨ p1001)
    (h5943 : p1006 ∨ p1010)
    (h5944 : p1006 ∨ p1011)
    (h5946 : p1006 ∨ p1013)
    (h5947 : p1006 ∨ p1014)
    (h5873 : p419 ∨ p1001 ∨ (¬ p1010) ∨ (¬ p1011) ∨ (¬ p1012) ∨ (¬ p1013) ∨ (¬ p1014)) : p1006 ∨ p1001 ∨ p419 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1006) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1001) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p419) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1012 := by
    rcases h24393 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u2 q1)
    · exact False.elim (u1 q2)
  have u4 : p1010 := by
    rcases h5943 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1011 := by
    rcases h5944 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1013 := by
    rcases h5946 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1014 := by
    rcases h5947 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5873 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24416 (p419 p1001 p1007 p1010 p1011 p1012 p1013 p1014 : Prop)
    (h24393 : p1012 ∨ p419 ∨ p1001)
    (h5948 : p1007 ∨ p1010)
    (h5949 : p1007 ∨ p1011)
    (h5951 : p1007 ∨ p1013)
    (h5952 : p1007 ∨ p1014)
    (h5873 : p419 ∨ p1001 ∨ (¬ p1010) ∨ (¬ p1011) ∨ (¬ p1012) ∨ (¬ p1013) ∨ (¬ p1014)) : p1007 ∨ p1001 ∨ p419 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1007) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1001) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p419) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1012 := by
    rcases h24393 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u2 q1)
    · exact False.elim (u1 q2)
  have u4 : p1010 := by
    rcases h5948 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1011 := by
    rcases h5949 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1013 := by
    rcases h5951 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1014 := by
    rcases h5952 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5873 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24417 (p419 p1001 p1008 p1010 p1011 p1012 p1013 p1014 : Prop)
    (h24393 : p1012 ∨ p419 ∨ p1001)
    (h5953 : p1008 ∨ p1010)
    (h5954 : p1008 ∨ p1011)
    (h5956 : p1008 ∨ p1013)
    (h5957 : p1008 ∨ p1014)
    (h5873 : p419 ∨ p1001 ∨ (¬ p1010) ∨ (¬ p1011) ∨ (¬ p1012) ∨ (¬ p1013) ∨ (¬ p1014)) : p1008 ∨ p1001 ∨ p419 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1008) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1001) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p419) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1012 := by
    rcases h24393 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u2 q1)
    · exact False.elim (u1 q2)
  have u4 : p1010 := by
    rcases h5953 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1011 := by
    rcases h5954 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1013 := by
    rcases h5956 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1014 := by
    rcases h5957 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5873 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24418 (p419 p1001 p1005 p1006 p1007 p1008 p1009 p1010 p1011 p1012 p1013 p1014 : Prop)
    (h24393 : p1012 ∨ p419 ∨ p1001)
    (h24414 : p1005 ∨ p1001 ∨ p419)
    (h24415 : p1006 ∨ p1001 ∨ p419)
    (h24416 : p1007 ∨ p1001 ∨ p419)
    (h24417 : p1008 ∨ p1001 ∨ p419)
    (h5848 : p419 ∨ p1001 ∨ (¬ p1005) ∨ (¬ p1006) ∨ (¬ p1007) ∨ (¬ p1008) ∨ (¬ p1009))
    (h5958 : p1009 ∨ p1010)
    (h5959 : p1009 ∨ p1011)
    (h5961 : p1009 ∨ p1013)
    (h5962 : p1009 ∨ p1014)
    (h5873 : p419 ∨ p1001 ∨ (¬ p1010) ∨ (¬ p1011) ∨ (¬ p1012) ∨ (¬ p1013) ∨ (¬ p1014)) : p1001 ∨ p419 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1001) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p419) := fun hu => hn (Or.inr hu)
  have u2 : p1012 := by
    rcases h24393 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u3 : p1005 := by
    rcases h24414 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1006 := by
    rcases h24415 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1007 := by
    rcases h24416 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p1008 := by
    rcases h24417 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p1009) := by
    rcases h5848 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p1010 := by
    rcases h5958 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p1011 := by
    rcases h5959 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p1013 := by
    rcases h5961 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p1014 := by
    rcases h5962 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h5873 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step24419 (p346 p351 p356 p357 p358 p359 p360 p361 : Prop)
    (h1945 : p356 ∨ p357)
    (h1946 : p356 ∨ p358)
    (h1947 : p356 ∨ p359)
    (h1948 : p356 ∨ p360)
    (h1864 : p346 ∨ p351 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361)) : p356 ∨ (¬ p361) ∨ p351 ∨ p346 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p356) := fun hu => hn (Or.inl hu)
  have u1 : p361 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p351) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p346) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p357 := by
    rcases h1945 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p358 := by
    rcases h1946 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p359 := by
    rcases h1947 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p360 := by
    rcases h1948 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1864 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24420 (p346 p351 p352 p353 p354 p355 p356 p357 : Prop)
    (h1925 : p352 ∨ p357)
    (h1930 : p353 ∨ p357)
    (h1935 : p354 ∨ p357)
    (h1940 : p355 ∨ p357)
    (h1839 : p346 ∨ p351 ∨ (¬ p352) ∨ (¬ p353) ∨ (¬ p354) ∨ (¬ p355) ∨ (¬ p356)) : p357 ∨ (¬ p356) ∨ p351 ∨ p346 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p357) := fun hu => hn (Or.inl hu)
  have u1 : p356 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p351) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p346) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p352 := by
    rcases h1925 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p353 := by
    rcases h1930 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p354 := by
    rcases h1935 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p355 := by
    rcases h1940 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1839 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24421 (p346 p351 p352 p353 p354 p355 p356 p358 : Prop)
    (h1926 : p352 ∨ p358)
    (h1931 : p353 ∨ p358)
    (h1936 : p354 ∨ p358)
    (h1941 : p355 ∨ p358)
    (h1839 : p346 ∨ p351 ∨ (¬ p352) ∨ (¬ p353) ∨ (¬ p354) ∨ (¬ p355) ∨ (¬ p356)) : p358 ∨ (¬ p356) ∨ p351 ∨ p346 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p358) := fun hu => hn (Or.inl hu)
  have u1 : p356 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p351) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p346) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p352 := by
    rcases h1926 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p353 := by
    rcases h1931 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p354 := by
    rcases h1936 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p355 := by
    rcases h1941 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1839 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24422 (p346 p351 p352 p353 p354 p355 p356 p359 : Prop)
    (h1927 : p352 ∨ p359)
    (h1932 : p353 ∨ p359)
    (h1937 : p354 ∨ p359)
    (h1942 : p355 ∨ p359)
    (h1839 : p346 ∨ p351 ∨ (¬ p352) ∨ (¬ p353) ∨ (¬ p354) ∨ (¬ p355) ∨ (¬ p356)) : p359 ∨ (¬ p356) ∨ p351 ∨ p346 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p359) := fun hu => hn (Or.inl hu)
  have u1 : p356 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p351) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p346) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p352 := by
    rcases h1927 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p353 := by
    rcases h1932 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p354 := by
    rcases h1937 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p355 := by
    rcases h1942 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1839 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24423 (p346 p351 p352 p353 p354 p355 p356 p357 p358 p359 p360 p361 : Prop)
    (h24419 : p356 ∨ (¬ p361) ∨ p351 ∨ p346)
    (h24420 : p357 ∨ (¬ p356) ∨ p351 ∨ p346)
    (h24421 : p358 ∨ (¬ p356) ∨ p351 ∨ p346)
    (h24422 : p359 ∨ (¬ p356) ∨ p351 ∨ p346)
    (h1864 : p346 ∨ p351 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361))
    (h1928 : p352 ∨ p360)
    (h1933 : p353 ∨ p360)
    (h1938 : p354 ∨ p360)
    (h1943 : p355 ∨ p360)
    (h1839 : p346 ∨ p351 ∨ (¬ p352) ∨ (¬ p353) ∨ (¬ p354) ∨ (¬ p355) ∨ (¬ p356)) : (¬ p361) ∨ p351 ∨ p346 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p361 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p351) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p346) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p356 := by
    rcases h24419 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u4 : p357 := by
    rcases h24420 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u5 : p358 := by
    rcases h24421 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u6 : p359 := by
    rcases h24422 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u7 : (¬ p360) := by
    rcases h1864 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u6)
    · exact q5
    · exact False.elim (q6 u0)
  have u8 : p352 := by
    rcases h1928 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p353 := by
    rcases h1933 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p354 := by
    rcases h1938 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p355 := by
    rcases h1943 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h1839 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u3)

theorem step24424 (p346 p351 p352 p353 p354 p355 p356 p361 : Prop)
    (h24423 : (¬ p361) ∨ p351 ∨ p346)
    (h1929 : p352 ∨ p361)
    (h1934 : p353 ∨ p361)
    (h1939 : p354 ∨ p361)
    (h1944 : p355 ∨ p361)
    (h1949 : p356 ∨ p361)
    (h1839 : p346 ∨ p351 ∨ (¬ p352) ∨ (¬ p353) ∨ (¬ p354) ∨ (¬ p355) ∨ (¬ p356)) : p351 ∨ p346 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p351) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p346) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p361) := by
    rcases h24423 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p352 := by
    rcases h1929 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : p353 := by
    rcases h1934 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p354 := by
    rcases h1939 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p355 := by
    rcases h1944 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p356 := by
    rcases h1949 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h1839 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24425 (p1035 p1469 p1474 p1475 p1476 p1477 p1478 p1482 : Prop)
    (h9012 : p1474 ∨ p1482)
    (h9017 : p1475 ∨ p1482)
    (h9022 : p1476 ∨ p1482)
    (h9027 : p1477 ∨ p1482)
    (h9032 : p1478 ∨ p1482)
    (h8931 : p1035 ∨ p1469 ∨ (¬ p1474) ∨ (¬ p1475) ∨ (¬ p1476) ∨ (¬ p1477) ∨ (¬ p1478)) : p1482 ∨ p1469 ∨ p1035 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1482) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1469) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1035) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1474 := by
    rcases h9012 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1475 := by
    rcases h9017 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1476 := by
    rcases h9022 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1477 := by
    rcases h9027 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1478 := by
    rcases h9032 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8931 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24426 (p1035 p1469 p1474 p1479 p1480 p1481 p1482 p1483 : Prop)
    (h24425 : p1482 ∨ p1469 ∨ p1035)
    (h9009 : p1474 ∨ p1479)
    (h9010 : p1474 ∨ p1480)
    (h9011 : p1474 ∨ p1481)
    (h9013 : p1474 ∨ p1483)
    (h8956 : p1035 ∨ p1469 ∨ (¬ p1479) ∨ (¬ p1480) ∨ (¬ p1481) ∨ (¬ p1482) ∨ (¬ p1483)) : p1474 ∨ p1469 ∨ p1035 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1474) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1469) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1035) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1482 := by
    rcases h24425 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1479 := by
    rcases h9009 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1480 := by
    rcases h9010 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1481 := by
    rcases h9011 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1483 := by
    rcases h9013 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8956 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24427 (p1035 p1469 p1475 p1479 p1480 p1481 p1482 p1483 : Prop)
    (h24425 : p1482 ∨ p1469 ∨ p1035)
    (h9014 : p1475 ∨ p1479)
    (h9015 : p1475 ∨ p1480)
    (h9016 : p1475 ∨ p1481)
    (h9018 : p1475 ∨ p1483)
    (h8956 : p1035 ∨ p1469 ∨ (¬ p1479) ∨ (¬ p1480) ∨ (¬ p1481) ∨ (¬ p1482) ∨ (¬ p1483)) : p1475 ∨ p1469 ∨ p1035 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1475) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1469) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1035) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1482 := by
    rcases h24425 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1479 := by
    rcases h9014 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1480 := by
    rcases h9015 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1481 := by
    rcases h9016 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1483 := by
    rcases h9018 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8956 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24428 (p1035 p1469 p1476 p1479 p1480 p1481 p1482 p1483 : Prop)
    (h24425 : p1482 ∨ p1469 ∨ p1035)
    (h9019 : p1476 ∨ p1479)
    (h9020 : p1476 ∨ p1480)
    (h9021 : p1476 ∨ p1481)
    (h9023 : p1476 ∨ p1483)
    (h8956 : p1035 ∨ p1469 ∨ (¬ p1479) ∨ (¬ p1480) ∨ (¬ p1481) ∨ (¬ p1482) ∨ (¬ p1483)) : p1476 ∨ p1469 ∨ p1035 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1476) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1469) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1035) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1482 := by
    rcases h24425 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1479 := by
    rcases h9019 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1480 := by
    rcases h9020 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1481 := by
    rcases h9021 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1483 := by
    rcases h9023 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8956 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24429 (p1035 p1469 p1477 p1479 p1480 p1481 p1482 p1483 : Prop)
    (h24425 : p1482 ∨ p1469 ∨ p1035)
    (h9024 : p1477 ∨ p1479)
    (h9025 : p1477 ∨ p1480)
    (h9026 : p1477 ∨ p1481)
    (h9028 : p1477 ∨ p1483)
    (h8956 : p1035 ∨ p1469 ∨ (¬ p1479) ∨ (¬ p1480) ∨ (¬ p1481) ∨ (¬ p1482) ∨ (¬ p1483)) : p1477 ∨ p1469 ∨ p1035 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1477) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1469) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1035) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1482 := by
    rcases h24425 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1479 := by
    rcases h9024 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1480 := by
    rcases h9025 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1481 := by
    rcases h9026 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1483 := by
    rcases h9028 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8956 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24430 (p1035 p1469 p1474 p1475 p1476 p1477 p1478 p1479 p1480 p1481 p1482 p1483 : Prop)
    (h24425 : p1482 ∨ p1469 ∨ p1035)
    (h24426 : p1474 ∨ p1469 ∨ p1035)
    (h24427 : p1475 ∨ p1469 ∨ p1035)
    (h24428 : p1476 ∨ p1469 ∨ p1035)
    (h24429 : p1477 ∨ p1469 ∨ p1035)
    (h8931 : p1035 ∨ p1469 ∨ (¬ p1474) ∨ (¬ p1475) ∨ (¬ p1476) ∨ (¬ p1477) ∨ (¬ p1478))
    (h9029 : p1478 ∨ p1479)
    (h9030 : p1478 ∨ p1480)
    (h9031 : p1478 ∨ p1481)
    (h9033 : p1478 ∨ p1483)
    (h8956 : p1035 ∨ p1469 ∨ (¬ p1479) ∨ (¬ p1480) ∨ (¬ p1481) ∨ (¬ p1482) ∨ (¬ p1483)) : p1469 ∨ p1035 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1469) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1035) := fun hu => hn (Or.inr hu)
  have u2 : p1482 := by
    rcases h24425 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1474 := by
    rcases h24426 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1475 := by
    rcases h24427 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1476 := by
    rcases h24428 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p1477 := by
    rcases h24429 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p1478) := by
    rcases h8931 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p1479 := by
    rcases h9029 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p1480 := by
    rcases h9030 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p1481 := by
    rcases h9031 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p1483 := by
    rcases h9033 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h8956 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u11)

theorem step24431 (p424 p797 p804 p805 p806 p807 p808 p811 : Prop)
    (h4645 : p804 ∨ p811)
    (h4650 : p805 ∨ p811)
    (h4655 : p806 ∨ p811)
    (h4660 : p807 ∨ p811)
    (h4665 : p808 ∨ p811)
    (h4545 : p424 ∨ p797 ∨ (¬ p804) ∨ (¬ p805) ∨ (¬ p806) ∨ (¬ p807) ∨ (¬ p808)) : p811 ∨ p797 ∨ p424 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p811) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p797) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p424) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p804 := by
    rcases h4645 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p805 := by
    rcases h4650 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p806 := by
    rcases h4655 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p807 := by
    rcases h4660 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p808 := by
    rcases h4665 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4545 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24432 (p424 p797 p804 p809 p810 p811 p812 p813 : Prop)
    (h24431 : p811 ∨ p797 ∨ p424)
    (h4643 : p804 ∨ p809)
    (h4644 : p804 ∨ p810)
    (h4646 : p804 ∨ p812)
    (h4647 : p804 ∨ p813)
    (h4570 : p424 ∨ p797 ∨ (¬ p809) ∨ (¬ p810) ∨ (¬ p811) ∨ (¬ p812) ∨ (¬ p813)) : p804 ∨ p797 ∨ p424 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p804) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p797) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p424) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p811 := by
    rcases h24431 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p809 := by
    rcases h4643 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p810 := by
    rcases h4644 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p812 := by
    rcases h4646 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p813 := by
    rcases h4647 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4570 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24433 (p424 p797 p805 p809 p810 p811 p812 p813 : Prop)
    (h24431 : p811 ∨ p797 ∨ p424)
    (h4648 : p805 ∨ p809)
    (h4649 : p805 ∨ p810)
    (h4651 : p805 ∨ p812)
    (h4652 : p805 ∨ p813)
    (h4570 : p424 ∨ p797 ∨ (¬ p809) ∨ (¬ p810) ∨ (¬ p811) ∨ (¬ p812) ∨ (¬ p813)) : p805 ∨ p797 ∨ p424 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p805) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p797) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p424) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p811 := by
    rcases h24431 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p809 := by
    rcases h4648 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p810 := by
    rcases h4649 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p812 := by
    rcases h4651 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p813 := by
    rcases h4652 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4570 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24434 (p424 p797 p806 p809 p810 p811 p812 p813 : Prop)
    (h24431 : p811 ∨ p797 ∨ p424)
    (h4653 : p806 ∨ p809)
    (h4654 : p806 ∨ p810)
    (h4656 : p806 ∨ p812)
    (h4657 : p806 ∨ p813)
    (h4570 : p424 ∨ p797 ∨ (¬ p809) ∨ (¬ p810) ∨ (¬ p811) ∨ (¬ p812) ∨ (¬ p813)) : p806 ∨ p797 ∨ p424 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p806) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p797) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p424) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p811 := by
    rcases h24431 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p809 := by
    rcases h4653 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p810 := by
    rcases h4654 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p812 := by
    rcases h4656 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p813 := by
    rcases h4657 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4570 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24435 (p424 p797 p807 p809 p810 p811 p812 p813 : Prop)
    (h24431 : p811 ∨ p797 ∨ p424)
    (h4658 : p807 ∨ p809)
    (h4659 : p807 ∨ p810)
    (h4661 : p807 ∨ p812)
    (h4662 : p807 ∨ p813)
    (h4570 : p424 ∨ p797 ∨ (¬ p809) ∨ (¬ p810) ∨ (¬ p811) ∨ (¬ p812) ∨ (¬ p813)) : p807 ∨ p797 ∨ p424 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p807) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p797) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p424) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p811 := by
    rcases h24431 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p809 := by
    rcases h4658 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p810 := by
    rcases h4659 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p812 := by
    rcases h4661 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p813 := by
    rcases h4662 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4570 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24436 (p424 p797 p804 p805 p806 p807 p808 p809 p810 p811 p812 p813 : Prop)
    (h24431 : p811 ∨ p797 ∨ p424)
    (h24432 : p804 ∨ p797 ∨ p424)
    (h24433 : p805 ∨ p797 ∨ p424)
    (h24434 : p806 ∨ p797 ∨ p424)
    (h24435 : p807 ∨ p797 ∨ p424)
    (h4545 : p424 ∨ p797 ∨ (¬ p804) ∨ (¬ p805) ∨ (¬ p806) ∨ (¬ p807) ∨ (¬ p808))
    (h4663 : p808 ∨ p809)
    (h4664 : p808 ∨ p810)
    (h4666 : p808 ∨ p812)
    (h4667 : p808 ∨ p813)
    (h4570 : p424 ∨ p797 ∨ (¬ p809) ∨ (¬ p810) ∨ (¬ p811) ∨ (¬ p812) ∨ (¬ p813)) : p797 ∨ p424 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p797) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p424) := fun hu => hn (Or.inr hu)
  have u2 : p811 := by
    rcases h24431 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p804 := by
    rcases h24432 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p805 := by
    rcases h24433 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p806 := by
    rcases h24434 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p807 := by
    rcases h24435 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p808) := by
    rcases h4545 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p809 := by
    rcases h4663 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p810 := by
    rcases h4664 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p812 := by
    rcases h4666 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p813 := by
    rcases h4667 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h4570 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step24437 (p226 p560 p564 p565 p566 p567 p568 p572 : Prop)
    (h3215 : p564 ∨ p572)
    (h3220 : p565 ∨ p572)
    (h3225 : p566 ∨ p572)
    (h3230 : p567 ∨ p572)
    (h3235 : p568 ∨ p572)
    (h3122 : p226 ∨ p560 ∨ (¬ p564) ∨ (¬ p565) ∨ (¬ p566) ∨ (¬ p567) ∨ (¬ p568)) : p572 ∨ p560 ∨ p226 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p572) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p560) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p226) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p564 := by
    rcases h3215 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p565 := by
    rcases h3220 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p566 := by
    rcases h3225 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p567 := by
    rcases h3230 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p568 := by
    rcases h3235 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3122 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24438 (p226 p560 p564 p569 p570 p571 p572 p573 : Prop)
    (h24437 : p572 ∨ p560 ∨ p226)
    (h3212 : p564 ∨ p569)
    (h3213 : p564 ∨ p570)
    (h3214 : p564 ∨ p571)
    (h3216 : p564 ∨ p573)
    (h3147 : p226 ∨ p560 ∨ (¬ p569) ∨ (¬ p570) ∨ (¬ p571) ∨ (¬ p572) ∨ (¬ p573)) : p564 ∨ p560 ∨ p226 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p564) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p560) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p226) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p572 := by
    rcases h24437 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p569 := by
    rcases h3212 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p570 := by
    rcases h3213 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p571 := by
    rcases h3214 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p573 := by
    rcases h3216 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3147 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24439 (p226 p560 p565 p569 p570 p571 p572 p573 : Prop)
    (h24437 : p572 ∨ p560 ∨ p226)
    (h3217 : p565 ∨ p569)
    (h3218 : p565 ∨ p570)
    (h3219 : p565 ∨ p571)
    (h3221 : p565 ∨ p573)
    (h3147 : p226 ∨ p560 ∨ (¬ p569) ∨ (¬ p570) ∨ (¬ p571) ∨ (¬ p572) ∨ (¬ p573)) : p565 ∨ p560 ∨ p226 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p565) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p560) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p226) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p572 := by
    rcases h24437 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p569 := by
    rcases h3217 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p570 := by
    rcases h3218 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p571 := by
    rcases h3219 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p573 := by
    rcases h3221 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3147 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24440 (p226 p560 p566 p569 p570 p571 p572 p573 : Prop)
    (h24437 : p572 ∨ p560 ∨ p226)
    (h3222 : p566 ∨ p569)
    (h3223 : p566 ∨ p570)
    (h3224 : p566 ∨ p571)
    (h3226 : p566 ∨ p573)
    (h3147 : p226 ∨ p560 ∨ (¬ p569) ∨ (¬ p570) ∨ (¬ p571) ∨ (¬ p572) ∨ (¬ p573)) : p566 ∨ p560 ∨ p226 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p566) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p560) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p226) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p572 := by
    rcases h24437 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p569 := by
    rcases h3222 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p570 := by
    rcases h3223 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p571 := by
    rcases h3224 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p573 := by
    rcases h3226 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3147 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24441 (p226 p560 p567 p569 p570 p571 p572 p573 : Prop)
    (h24437 : p572 ∨ p560 ∨ p226)
    (h3227 : p567 ∨ p569)
    (h3228 : p567 ∨ p570)
    (h3229 : p567 ∨ p571)
    (h3231 : p567 ∨ p573)
    (h3147 : p226 ∨ p560 ∨ (¬ p569) ∨ (¬ p570) ∨ (¬ p571) ∨ (¬ p572) ∨ (¬ p573)) : p567 ∨ p560 ∨ p226 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p567) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p560) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p226) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p572 := by
    rcases h24437 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p569 := by
    rcases h3227 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p570 := by
    rcases h3228 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p571 := by
    rcases h3229 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p573 := by
    rcases h3231 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3147 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24442 (p226 p560 p564 p565 p566 p567 p568 p569 p570 p571 p572 p573 : Prop)
    (h24437 : p572 ∨ p560 ∨ p226)
    (h24438 : p564 ∨ p560 ∨ p226)
    (h24439 : p565 ∨ p560 ∨ p226)
    (h24440 : p566 ∨ p560 ∨ p226)
    (h24441 : p567 ∨ p560 ∨ p226)
    (h3122 : p226 ∨ p560 ∨ (¬ p564) ∨ (¬ p565) ∨ (¬ p566) ∨ (¬ p567) ∨ (¬ p568))
    (h3232 : p568 ∨ p569)
    (h3233 : p568 ∨ p570)
    (h3234 : p568 ∨ p571)
    (h3236 : p568 ∨ p573)
    (h3147 : p226 ∨ p560 ∨ (¬ p569) ∨ (¬ p570) ∨ (¬ p571) ∨ (¬ p572) ∨ (¬ p573)) : p560 ∨ p226 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p560) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p226) := fun hu => hn (Or.inr hu)
  have u2 : p572 := by
    rcases h24437 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p564 := by
    rcases h24438 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p565 := by
    rcases h24439 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p566 := by
    rcases h24440 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p567 := by
    rcases h24441 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p568) := by
    rcases h3122 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p569 := by
    rcases h3232 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p570 := by
    rcases h3233 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p571 := by
    rcases h3234 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p573 := by
    rcases h3236 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h3147 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u11)

theorem step24449 (p899 p906 p907 p908 p909 p910 p911 p915 : Prop)
    (h5304 : p907 ∨ p915)
    (h5309 : p908 ∨ p915)
    (h5314 : p909 ∨ p915)
    (h5319 : p910 ∨ p915)
    (h5324 : p911 ∨ p915)
    (h5210 : p899 ∨ p906 ∨ (¬ p907) ∨ (¬ p908) ∨ (¬ p909) ∨ (¬ p910) ∨ (¬ p911)) : p915 ∨ p906 ∨ p899 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p915) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p906) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p899) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p907 := by
    rcases h5304 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p908 := by
    rcases h5309 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p909 := by
    rcases h5314 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p910 := by
    rcases h5319 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p911 := by
    rcases h5324 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5210 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24450 (p899 p906 p907 p912 p913 p914 p915 p916 : Prop)
    (h24449 : p915 ∨ p906 ∨ p899)
    (h5301 : p907 ∨ p912)
    (h5302 : p907 ∨ p913)
    (h5303 : p907 ∨ p914)
    (h5305 : p907 ∨ p916)
    (h5235 : p899 ∨ p906 ∨ (¬ p912) ∨ (¬ p913) ∨ (¬ p914) ∨ (¬ p915) ∨ (¬ p916)) : p907 ∨ p906 ∨ p899 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p907) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p906) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p899) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p915 := by
    rcases h24449 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p912 := by
    rcases h5301 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p913 := by
    rcases h5302 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p914 := by
    rcases h5303 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p916 := by
    rcases h5305 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5235 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24451 (p899 p906 p908 p912 p913 p914 p915 p916 : Prop)
    (h24449 : p915 ∨ p906 ∨ p899)
    (h5306 : p908 ∨ p912)
    (h5307 : p908 ∨ p913)
    (h5308 : p908 ∨ p914)
    (h5310 : p908 ∨ p916)
    (h5235 : p899 ∨ p906 ∨ (¬ p912) ∨ (¬ p913) ∨ (¬ p914) ∨ (¬ p915) ∨ (¬ p916)) : p908 ∨ p906 ∨ p899 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p908) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p906) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p899) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p915 := by
    rcases h24449 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p912 := by
    rcases h5306 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p913 := by
    rcases h5307 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p914 := by
    rcases h5308 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p916 := by
    rcases h5310 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5235 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24452 (p899 p906 p909 p912 p913 p914 p915 p916 : Prop)
    (h24449 : p915 ∨ p906 ∨ p899)
    (h5311 : p909 ∨ p912)
    (h5312 : p909 ∨ p913)
    (h5313 : p909 ∨ p914)
    (h5315 : p909 ∨ p916)
    (h5235 : p899 ∨ p906 ∨ (¬ p912) ∨ (¬ p913) ∨ (¬ p914) ∨ (¬ p915) ∨ (¬ p916)) : p909 ∨ p906 ∨ p899 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p909) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p906) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p899) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p915 := by
    rcases h24449 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p912 := by
    rcases h5311 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p913 := by
    rcases h5312 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p914 := by
    rcases h5313 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p916 := by
    rcases h5315 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5235 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24453 (p899 p906 p910 p912 p913 p914 p915 p916 : Prop)
    (h24449 : p915 ∨ p906 ∨ p899)
    (h5316 : p910 ∨ p912)
    (h5317 : p910 ∨ p913)
    (h5318 : p910 ∨ p914)
    (h5320 : p910 ∨ p916)
    (h5235 : p899 ∨ p906 ∨ (¬ p912) ∨ (¬ p913) ∨ (¬ p914) ∨ (¬ p915) ∨ (¬ p916)) : p910 ∨ p906 ∨ p899 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p910) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p906) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p899) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p915 := by
    rcases h24449 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p912 := by
    rcases h5316 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p913 := by
    rcases h5317 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p914 := by
    rcases h5318 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p916 := by
    rcases h5320 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5235 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24454 (p899 p906 p907 p908 p909 p910 p911 p912 p913 p914 p915 p916 : Prop)
    (h24449 : p915 ∨ p906 ∨ p899)
    (h24450 : p907 ∨ p906 ∨ p899)
    (h24451 : p908 ∨ p906 ∨ p899)
    (h24452 : p909 ∨ p906 ∨ p899)
    (h24453 : p910 ∨ p906 ∨ p899)
    (h5210 : p899 ∨ p906 ∨ (¬ p907) ∨ (¬ p908) ∨ (¬ p909) ∨ (¬ p910) ∨ (¬ p911))
    (h5321 : p911 ∨ p912)
    (h5322 : p911 ∨ p913)
    (h5323 : p911 ∨ p914)
    (h5325 : p911 ∨ p916)
    (h5235 : p899 ∨ p906 ∨ (¬ p912) ∨ (¬ p913) ∨ (¬ p914) ∨ (¬ p915) ∨ (¬ p916)) : p906 ∨ p899 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p906) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p899) := fun hu => hn (Or.inr hu)
  have u2 : p915 := by
    rcases h24449 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p907 := by
    rcases h24450 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p908 := by
    rcases h24451 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p909 := by
    rcases h24452 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p910 := by
    rcases h24453 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p911) := by
    rcases h5210 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p912 := by
    rcases h5321 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p913 := by
    rcases h5322 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p914 := by
    rcases h5323 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p916 := by
    rcases h5325 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h5235 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u11)

theorem step24456 (p899 p903 p911 p912 p913 p914 p915 p916 : Prop)
    (h5321 : p911 ∨ p912)
    (h5322 : p911 ∨ p913)
    (h5323 : p911 ∨ p914)
    (h5325 : p911 ∨ p916)
    (h5232 : p899 ∨ p903 ∨ (¬ p912) ∨ (¬ p913) ∨ (¬ p914) ∨ (¬ p915) ∨ (¬ p916)) : p911 ∨ (¬ p915) ∨ p903 ∨ p899 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p911) := fun hu => hn (Or.inl hu)
  have u1 : p915 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p903) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p899) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p912 := by
    rcases h5321 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p913 := by
    rcases h5322 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p914 := by
    rcases h5323 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p916 := by
    rcases h5325 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5232 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step24457 (p899 p903 p907 p908 p909 p910 p911 p916 : Prop)
    (h5305 : p907 ∨ p916)
    (h5310 : p908 ∨ p916)
    (h5315 : p909 ∨ p916)
    (h5320 : p910 ∨ p916)
    (h5207 : p899 ∨ p903 ∨ (¬ p907) ∨ (¬ p908) ∨ (¬ p909) ∨ (¬ p910) ∨ (¬ p911)) : p916 ∨ (¬ p911) ∨ p903 ∨ p899 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p916) := fun hu => hn (Or.inl hu)
  have u1 : p911 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p903) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p899) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p907 := by
    rcases h5305 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p908 := by
    rcases h5310 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p909 := by
    rcases h5315 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p910 := by
    rcases h5320 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5207 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24458 (p899 p903 p907 p908 p909 p910 p911 p912 : Prop)
    (h5301 : p907 ∨ p912)
    (h5306 : p908 ∨ p912)
    (h5311 : p909 ∨ p912)
    (h5316 : p910 ∨ p912)
    (h5207 : p899 ∨ p903 ∨ (¬ p907) ∨ (¬ p908) ∨ (¬ p909) ∨ (¬ p910) ∨ (¬ p911)) : p912 ∨ (¬ p911) ∨ p903 ∨ p899 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p912) := fun hu => hn (Or.inl hu)
  have u1 : p911 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p903) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p899) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p907 := by
    rcases h5301 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p908 := by
    rcases h5306 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p909 := by
    rcases h5311 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p910 := by
    rcases h5316 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5207 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24459 (p899 p903 p907 p908 p909 p910 p911 p913 : Prop)
    (h5302 : p907 ∨ p913)
    (h5307 : p908 ∨ p913)
    (h5312 : p909 ∨ p913)
    (h5317 : p910 ∨ p913)
    (h5207 : p899 ∨ p903 ∨ (¬ p907) ∨ (¬ p908) ∨ (¬ p909) ∨ (¬ p910) ∨ (¬ p911)) : p913 ∨ (¬ p911) ∨ p903 ∨ p899 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p913) := fun hu => hn (Or.inl hu)
  have u1 : p911 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p903) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p899) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p907 := by
    rcases h5302 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p908 := by
    rcases h5307 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p909 := by
    rcases h5312 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p910 := by
    rcases h5317 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5207 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24460 (p897 p899 p903 p907 p908 p909 p910 p911 p912 p913 p914 p915 p916 : Prop)
    (h24456 : p911 ∨ (¬ p915) ∨ p903 ∨ p899)
    (h24457 : p916 ∨ (¬ p911) ∨ p903 ∨ p899)
    (h24458 : p912 ∨ (¬ p911) ∨ p903 ∨ p899)
    (h24459 : p913 ∨ (¬ p911) ∨ p903 ∨ p899)
    (h5237 : p897 ∨ p903 ∨ (¬ p912) ∨ (¬ p913) ∨ (¬ p914) ∨ (¬ p915) ∨ (¬ p916))
    (h5303 : p907 ∨ p914)
    (h5308 : p908 ∨ p914)
    (h5313 : p909 ∨ p914)
    (h5318 : p910 ∨ p914)
    (h5207 : p899 ∨ p903 ∨ (¬ p907) ∨ (¬ p908) ∨ (¬ p909) ∨ (¬ p910) ∨ (¬ p911)) : (¬ p915) ∨ p903 ∨ p897 ∨ p899 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p915 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p903) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p899) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p911 := by
    rcases h24456 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u3 q3)
  have u5 : p916 := by
    rcases h24457 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u4)
    · exact False.elim (u1 q2)
    · exact False.elim (u3 q3)
  have u6 : p912 := by
    rcases h24458 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u4)
    · exact False.elim (u1 q2)
    · exact False.elim (u3 q3)
  have u7 : p913 := by
    rcases h24459 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u4)
    · exact False.elim (u1 q2)
    · exact False.elim (u3 q3)
  have u8 : (¬ p914) := by
    rcases h5237 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u6)
    · exact False.elim (q3 u7)
    · exact q4
    · exact False.elim (q5 u0)
    · exact False.elim (q6 u5)
  have u9 : p907 := by
    rcases h5303 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u10 : p908 := by
    rcases h5308 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u11 : p909 := by
    rcases h5313 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u12 : p910 := by
    rcases h5318 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h5207 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u12)
  · exact False.elim (q6 u4)

theorem step24461 (p897 p899 p903 p907 p908 p909 p910 p911 p915 : Prop)
    (h24460 : (¬ p915) ∨ p903 ∨ p897 ∨ p899)
    (h5304 : p907 ∨ p915)
    (h5309 : p908 ∨ p915)
    (h5314 : p909 ∨ p915)
    (h5319 : p910 ∨ p915)
    (h5324 : p911 ∨ p915)
    (h5207 : p899 ∨ p903 ∨ (¬ p907) ∨ (¬ p908) ∨ (¬ p909) ∨ (¬ p910) ∨ (¬ p911)) : p903 ∨ p897 ∨ p899 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p903) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p897) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p899) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : (¬ p915) := by
    rcases h24460 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u4 : p907 := by
    rcases h5304 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u5 : p908 := by
    rcases h5309 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p909 := by
    rcases h5314 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p910 := by
    rcases h5319 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p911 := by
    rcases h5324 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h5207 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u8)

theorem step24463 (p899 p903 p907 p908 p909 p910 p911 p915 : Prop)
    (h5304 : p907 ∨ p915)
    (h5309 : p908 ∨ p915)
    (h5314 : p909 ∨ p915)
    (h5319 : p910 ∨ p915)
    (h5324 : p911 ∨ p915)
    (h5207 : p899 ∨ p903 ∨ (¬ p907) ∨ (¬ p908) ∨ (¬ p909) ∨ (¬ p910) ∨ (¬ p911)) : p915 ∨ p903 ∨ p899 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p915) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p903) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p899) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p907 := by
    rcases h5304 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p908 := by
    rcases h5309 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p909 := by
    rcases h5314 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p910 := by
    rcases h5319 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p911 := by
    rcases h5324 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5207 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24464 (p897 p899 p903 p904 p907 p908 p909 p910 p911 p912 p913 p914 p915 p916 : Prop)
    (h24461 : p903 ∨ p897 ∨ p899)
    (h10282 : (¬ p897) ∨ (¬ p904))
    (h24463 : p915 ∨ p903 ∨ p899)
    (h24456 : p911 ∨ (¬ p915) ∨ p903 ∨ p899)
    (h24457 : p916 ∨ (¬ p911) ∨ p903 ∨ p899)
    (h24458 : p912 ∨ (¬ p911) ∨ p903 ∨ p899)
    (h24459 : p913 ∨ (¬ p911) ∨ p903 ∨ p899)
    (h5233 : p899 ∨ p904 ∨ (¬ p912) ∨ (¬ p913) ∨ (¬ p914) ∨ (¬ p915) ∨ (¬ p916))
    (h5303 : p907 ∨ p914)
    (h5308 : p908 ∨ p914)
    (h5313 : p909 ∨ p914)
    (h5318 : p910 ∨ p914)
    (h5207 : p899 ∨ p903 ∨ (¬ p907) ∨ (¬ p908) ∨ (¬ p909) ∨ (¬ p910) ∨ (¬ p911)) : p903 ∨ p899 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p903) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p899) := fun hu => hn (Or.inr hu)
  have u2 : p897 := by
    rcases h24461 with q0 | q1 | q2
    · exact False.elim (u0 q0)
    · exact q1
    · exact False.elim (u1 q2)
  have u3 : (¬ p904) := by
    rcases h10282 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u4 : p915 := by
    rcases h24463 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p911 := by
    rcases h24456 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u4)
    · exact False.elim (u0 q2)
    · exact False.elim (u1 q3)
  have u6 : p916 := by
    rcases h24457 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u5)
    · exact False.elim (u0 q2)
    · exact False.elim (u1 q3)
  have u7 : p912 := by
    rcases h24458 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u5)
    · exact False.elim (u0 q2)
    · exact False.elim (u1 q3)
  have u8 : p913 := by
    rcases h24459 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u5)
    · exact False.elim (u0 q2)
    · exact False.elim (u1 q3)
  have u9 : (¬ p914) := by
    rcases h5233 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u7)
    · exact False.elim (q3 u8)
    · exact q4
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u6)
  have u10 : p907 := by
    rcases h5303 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  have u11 : p908 := by
    rcases h5308 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  have u12 : p909 := by
    rcases h5313 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  have u13 : p910 := by
    rcases h5318 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h5207 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u12)
  · exact False.elim (q5 u13)
  · exact False.elim (q6 u5)

theorem step24465 (p41 p45 p63 p85 p156 p163 p170 p918 p923 p927 p928 p1099 : Prop)
    (h21444 : p41 ∨ p45)
    (h22211 : p85 ∨ p63)
    (h12049 : p85 ∨ (¬ p927) ∨ (¬ p1099))
    (h23359 : p927 ∨ p918)
    (h7049 : (¬ p918) ∨ (¬ p928))
    (h12299 : p45 ∨ (¬ p170) ∨ (¬ p918))
    (h22484 : p923 ∨ p928)
    (h22001 : p156 ∨ p170 ∨ p163)
    (h18407 : (¬ p41) ∨ (¬ p63) ∨ (¬ p156) ∨ (¬ p923) ∨ (¬ p1099)) : p85 ∨ p45 ∨ p163 ∨ (¬ p1099) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p85) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p45) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p41 := by
    rcases h21444 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p63 := by
    rcases h22211 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : (¬ p927) := by
    rcases h12049 with q0 | q1 | q2
    · exact False.elim (u0 q0)
    · exact q1
    · exact False.elim (q2 u3)
  have u7 : p918 := by
    rcases h23359 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : (¬ p928) := by
    rcases h7049 with q0 | q1
    · exact False.elim (q0 u7)
    · exact q1
  have u9 : (¬ p170) := by
    rcases h12299 with q0 | q1 | q2
    · exact False.elim (u1 q0)
    · exact q1
    · exact False.elim (q2 u7)
  have u10 : p923 := by
    rcases h22484 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u11 : p156 := by
    rcases h22001 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u9 q1)
    · exact False.elim (u2 q2)
  rcases h18407 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u3)

theorem step24467 (p479 p481 p484 p485 p486 p487 p488 p491 : Prop)
    (h2704 : p484 ∨ p491)
    (h2709 : p485 ∨ p491)
    (h2714 : p486 ∨ p491)
    (h2719 : p487 ∨ p491)
    (h2724 : p488 ∨ p491)
    (h2624 : p479 ∨ p481 ∨ (¬ p484) ∨ (¬ p485) ∨ (¬ p486) ∨ (¬ p487) ∨ (¬ p488)) : p491 ∨ p479 ∨ p481 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p491) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p479) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p481) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p484 := by
    rcases h2704 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p485 := by
    rcases h2709 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p486 := by
    rcases h2714 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p487 := by
    rcases h2719 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p488 := by
    rcases h2724 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2624 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24468 (p479 p481 p484 p489 p490 p491 p492 p493 : Prop)
    (h24467 : p491 ∨ p479 ∨ p481)
    (h2702 : p484 ∨ p489)
    (h2703 : p484 ∨ p490)
    (h2705 : p484 ∨ p492)
    (h2706 : p484 ∨ p493)
    (h2649 : p479 ∨ p481 ∨ (¬ p489) ∨ (¬ p490) ∨ (¬ p491) ∨ (¬ p492) ∨ (¬ p493)) : p484 ∨ p479 ∨ p481 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p484) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p479) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p481) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p491 := by
    rcases h24467 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p489 := by
    rcases h2702 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p490 := by
    rcases h2703 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p492 := by
    rcases h2705 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p493 := by
    rcases h2706 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2649 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24469 (p479 p481 p485 p489 p490 p491 p492 p493 : Prop)
    (h24467 : p491 ∨ p479 ∨ p481)
    (h2707 : p485 ∨ p489)
    (h2708 : p485 ∨ p490)
    (h2710 : p485 ∨ p492)
    (h2711 : p485 ∨ p493)
    (h2649 : p479 ∨ p481 ∨ (¬ p489) ∨ (¬ p490) ∨ (¬ p491) ∨ (¬ p492) ∨ (¬ p493)) : p485 ∨ p479 ∨ p481 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p485) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p479) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p481) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p491 := by
    rcases h24467 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p489 := by
    rcases h2707 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p490 := by
    rcases h2708 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p492 := by
    rcases h2710 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p493 := by
    rcases h2711 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2649 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24470 (p479 p481 p486 p489 p490 p491 p492 p493 : Prop)
    (h24467 : p491 ∨ p479 ∨ p481)
    (h2712 : p486 ∨ p489)
    (h2713 : p486 ∨ p490)
    (h2715 : p486 ∨ p492)
    (h2716 : p486 ∨ p493)
    (h2649 : p479 ∨ p481 ∨ (¬ p489) ∨ (¬ p490) ∨ (¬ p491) ∨ (¬ p492) ∨ (¬ p493)) : p486 ∨ p479 ∨ p481 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p486) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p479) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p481) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p491 := by
    rcases h24467 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p489 := by
    rcases h2712 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p490 := by
    rcases h2713 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p492 := by
    rcases h2715 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p493 := by
    rcases h2716 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2649 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24471 (p479 p481 p487 p489 p490 p491 p492 p493 : Prop)
    (h24467 : p491 ∨ p479 ∨ p481)
    (h2717 : p487 ∨ p489)
    (h2718 : p487 ∨ p490)
    (h2720 : p487 ∨ p492)
    (h2721 : p487 ∨ p493)
    (h2649 : p479 ∨ p481 ∨ (¬ p489) ∨ (¬ p490) ∨ (¬ p491) ∨ (¬ p492) ∨ (¬ p493)) : p487 ∨ p479 ∨ p481 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p487) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p479) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p481) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p491 := by
    rcases h24467 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p489 := by
    rcases h2717 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p490 := by
    rcases h2718 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p492 := by
    rcases h2720 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p493 := by
    rcases h2721 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2649 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24472 (p479 p481 p484 p485 p486 p487 p488 p489 p490 p491 p492 p493 : Prop)
    (h24467 : p491 ∨ p479 ∨ p481)
    (h24468 : p484 ∨ p479 ∨ p481)
    (h24469 : p485 ∨ p479 ∨ p481)
    (h24470 : p486 ∨ p479 ∨ p481)
    (h24471 : p487 ∨ p479 ∨ p481)
    (h2624 : p479 ∨ p481 ∨ (¬ p484) ∨ (¬ p485) ∨ (¬ p486) ∨ (¬ p487) ∨ (¬ p488))
    (h2722 : p488 ∨ p489)
    (h2723 : p488 ∨ p490)
    (h2725 : p488 ∨ p492)
    (h2726 : p488 ∨ p493)
    (h2649 : p479 ∨ p481 ∨ (¬ p489) ∨ (¬ p490) ∨ (¬ p491) ∨ (¬ p492) ∨ (¬ p493)) : p479 ∨ p481 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p479) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p481) := fun hu => hn (Or.inr hu)
  have u2 : p491 := by
    rcases h24467 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p484 := by
    rcases h24468 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p485 := by
    rcases h24469 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p486 := by
    rcases h24470 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p487 := by
    rcases h24471 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p488) := by
    rcases h2624 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u0 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p489 := by
    rcases h2722 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p490 := by
    rcases h2723 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p492 := by
    rcases h2725 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p493 := by
    rcases h2726 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h2649 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step24473 (p400 p404 p479 p996 p1226 p1333 : Prop)
    (h11322 : (¬ p404) ∨ (¬ p1226) ∨ (¬ p1333))
    (h17929 : (¬ p400) ∨ (¬ p479) ∨ (¬ p996) ∨ (¬ p1226) ∨ (¬ p1333))
    (h24130 : p400 ∨ p404) : (¬ p1226) ∨ (¬ p996) ∨ (¬ p1333) ∨ (¬ p479) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p479 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p404) := by
    rcases h11322 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u2)
  have u5 : (¬ p400) := by
    rcases h17929 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u2)
  rcases h24130 with q0 | q1
  · exact False.elim (u5 q0)
  · exact False.elim (u4 q1)

theorem step24474 (p19 p21 p32 p33 p34 p35 p36 p37 : Prop)
    (h125 : p32 ∨ p33)
    (h126 : p32 ∨ p34)
    (h127 : p32 ∨ p35)
    (h128 : p32 ∨ p36)
    (h37 : p19 ∨ p21 ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p36) ∨ (¬ p37)) : p32 ∨ (¬ p37) ∨ p21 ∨ p19 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p32) := fun hu => hn (Or.inl hu)
  have u1 : p37 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p21) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p19) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p33 := by
    rcases h125 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p34 := by
    rcases h126 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p35 := by
    rcases h127 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p36 := by
    rcases h128 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h37 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24475 (p19 p21 p28 p29 p30 p31 p32 p33 : Prop)
    (h105 : p28 ∨ p33)
    (h110 : p29 ∨ p33)
    (h115 : p30 ∨ p33)
    (h120 : p31 ∨ p33)
    (h12 : p19 ∨ p21 ∨ (¬ p28) ∨ (¬ p29) ∨ (¬ p30) ∨ (¬ p31) ∨ (¬ p32)) : p33 ∨ (¬ p32) ∨ p21 ∨ p19 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p33) := fun hu => hn (Or.inl hu)
  have u1 : p32 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p21) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p19) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p28 := by
    rcases h105 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p29 := by
    rcases h110 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p30 := by
    rcases h115 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p31 := by
    rcases h120 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h12 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24476 (p19 p21 p28 p29 p30 p31 p32 p34 : Prop)
    (h106 : p28 ∨ p34)
    (h111 : p29 ∨ p34)
    (h116 : p30 ∨ p34)
    (h121 : p31 ∨ p34)
    (h12 : p19 ∨ p21 ∨ (¬ p28) ∨ (¬ p29) ∨ (¬ p30) ∨ (¬ p31) ∨ (¬ p32)) : p34 ∨ (¬ p32) ∨ p21 ∨ p19 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p34) := fun hu => hn (Or.inl hu)
  have u1 : p32 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p21) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p19) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p28 := by
    rcases h106 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p29 := by
    rcases h111 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p30 := by
    rcases h116 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p31 := by
    rcases h121 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h12 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24477 (p19 p21 p28 p29 p30 p31 p32 p35 : Prop)
    (h107 : p28 ∨ p35)
    (h112 : p29 ∨ p35)
    (h117 : p30 ∨ p35)
    (h122 : p31 ∨ p35)
    (h12 : p19 ∨ p21 ∨ (¬ p28) ∨ (¬ p29) ∨ (¬ p30) ∨ (¬ p31) ∨ (¬ p32)) : p35 ∨ (¬ p32) ∨ p21 ∨ p19 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p35) := fun hu => hn (Or.inl hu)
  have u1 : p32 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p21) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p19) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p28 := by
    rcases h107 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p29 := by
    rcases h112 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p30 := by
    rcases h117 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p31 := by
    rcases h122 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h12 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24478 (p19 p21 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 : Prop)
    (h24474 : p32 ∨ (¬ p37) ∨ p21 ∨ p19)
    (h24475 : p33 ∨ (¬ p32) ∨ p21 ∨ p19)
    (h24476 : p34 ∨ (¬ p32) ∨ p21 ∨ p19)
    (h24477 : p35 ∨ (¬ p32) ∨ p21 ∨ p19)
    (h37 : p19 ∨ p21 ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p36) ∨ (¬ p37))
    (h108 : p28 ∨ p36)
    (h113 : p29 ∨ p36)
    (h118 : p30 ∨ p36)
    (h123 : p31 ∨ p36)
    (h12 : p19 ∨ p21 ∨ (¬ p28) ∨ (¬ p29) ∨ (¬ p30) ∨ (¬ p31) ∨ (¬ p32)) : (¬ p37) ∨ p21 ∨ p19 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p37 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p21) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p19) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p32 := by
    rcases h24474 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u4 : p33 := by
    rcases h24475 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u5 : p34 := by
    rcases h24476 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u6 : p35 := by
    rcases h24477 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u7 : (¬ p36) := by
    rcases h37 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u6)
    · exact q5
    · exact False.elim (q6 u0)
  have u8 : p28 := by
    rcases h108 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p29 := by
    rcases h113 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p30 := by
    rcases h118 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p31 := by
    rcases h123 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h12 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u3)

theorem step24479 (p19 p21 p28 p29 p30 p31 p32 p37 : Prop)
    (h24478 : (¬ p37) ∨ p21 ∨ p19)
    (h109 : p28 ∨ p37)
    (h114 : p29 ∨ p37)
    (h119 : p30 ∨ p37)
    (h124 : p31 ∨ p37)
    (h129 : p32 ∨ p37)
    (h12 : p19 ∨ p21 ∨ (¬ p28) ∨ (¬ p29) ∨ (¬ p30) ∨ (¬ p31) ∨ (¬ p32)) : p21 ∨ p19 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p21) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p19) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p37) := by
    rcases h24478 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p28 := by
    rcases h109 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : p29 := by
    rcases h114 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p30 := by
    rcases h119 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p31 := by
    rcases h124 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p32 := by
    rcases h129 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h12 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24480 (p438 p444 p445 p446 p447 p448 p449 p453 : Prop)
    (h2450 : p445 ∨ p453)
    (h2455 : p446 ∨ p453)
    (h2460 : p447 ∨ p453)
    (h2465 : p448 ∨ p453)
    (h2470 : p449 ∨ p453)
    (h2361 : p438 ∨ p444 ∨ (¬ p445) ∨ (¬ p446) ∨ (¬ p447) ∨ (¬ p448) ∨ (¬ p449)) : p453 ∨ p444 ∨ p438 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p453) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p444) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p438) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p445 := by
    rcases h2450 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p446 := by
    rcases h2455 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p447 := by
    rcases h2460 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p448 := by
    rcases h2465 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p449 := by
    rcases h2470 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2361 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24481 (p438 p444 p445 p450 p451 p452 p453 p454 : Prop)
    (h24480 : p453 ∨ p444 ∨ p438)
    (h2447 : p445 ∨ p450)
    (h2448 : p445 ∨ p451)
    (h2449 : p445 ∨ p452)
    (h2451 : p445 ∨ p454)
    (h2386 : p438 ∨ p444 ∨ (¬ p450) ∨ (¬ p451) ∨ (¬ p452) ∨ (¬ p453) ∨ (¬ p454)) : p445 ∨ p444 ∨ p438 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p445) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p444) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p438) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p453 := by
    rcases h24480 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p450 := by
    rcases h2447 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p451 := by
    rcases h2448 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p452 := by
    rcases h2449 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p454 := by
    rcases h2451 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2386 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24482 (p438 p444 p446 p450 p451 p452 p453 p454 : Prop)
    (h24480 : p453 ∨ p444 ∨ p438)
    (h2452 : p446 ∨ p450)
    (h2453 : p446 ∨ p451)
    (h2454 : p446 ∨ p452)
    (h2456 : p446 ∨ p454)
    (h2386 : p438 ∨ p444 ∨ (¬ p450) ∨ (¬ p451) ∨ (¬ p452) ∨ (¬ p453) ∨ (¬ p454)) : p446 ∨ p444 ∨ p438 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p446) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p444) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p438) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p453 := by
    rcases h24480 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p450 := by
    rcases h2452 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p451 := by
    rcases h2453 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p452 := by
    rcases h2454 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p454 := by
    rcases h2456 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2386 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24483 (p438 p444 p447 p450 p451 p452 p453 p454 : Prop)
    (h24480 : p453 ∨ p444 ∨ p438)
    (h2457 : p447 ∨ p450)
    (h2458 : p447 ∨ p451)
    (h2459 : p447 ∨ p452)
    (h2461 : p447 ∨ p454)
    (h2386 : p438 ∨ p444 ∨ (¬ p450) ∨ (¬ p451) ∨ (¬ p452) ∨ (¬ p453) ∨ (¬ p454)) : p447 ∨ p444 ∨ p438 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p447) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p444) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p438) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p453 := by
    rcases h24480 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p450 := by
    rcases h2457 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p451 := by
    rcases h2458 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p452 := by
    rcases h2459 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p454 := by
    rcases h2461 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2386 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24484 (p438 p444 p448 p450 p451 p452 p453 p454 : Prop)
    (h24480 : p453 ∨ p444 ∨ p438)
    (h2462 : p448 ∨ p450)
    (h2463 : p448 ∨ p451)
    (h2464 : p448 ∨ p452)
    (h2466 : p448 ∨ p454)
    (h2386 : p438 ∨ p444 ∨ (¬ p450) ∨ (¬ p451) ∨ (¬ p452) ∨ (¬ p453) ∨ (¬ p454)) : p448 ∨ p444 ∨ p438 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p448) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p444) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p438) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p453 := by
    rcases h24480 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p450 := by
    rcases h2462 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p451 := by
    rcases h2463 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p452 := by
    rcases h2464 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p454 := by
    rcases h2466 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2386 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24485 (p438 p444 p445 p446 p447 p448 p449 p450 p451 p452 p453 p454 : Prop)
    (h24480 : p453 ∨ p444 ∨ p438)
    (h24481 : p445 ∨ p444 ∨ p438)
    (h24482 : p446 ∨ p444 ∨ p438)
    (h24483 : p447 ∨ p444 ∨ p438)
    (h24484 : p448 ∨ p444 ∨ p438)
    (h2361 : p438 ∨ p444 ∨ (¬ p445) ∨ (¬ p446) ∨ (¬ p447) ∨ (¬ p448) ∨ (¬ p449))
    (h2467 : p449 ∨ p450)
    (h2468 : p449 ∨ p451)
    (h2469 : p449 ∨ p452)
    (h2471 : p449 ∨ p454)
    (h2386 : p438 ∨ p444 ∨ (¬ p450) ∨ (¬ p451) ∨ (¬ p452) ∨ (¬ p453) ∨ (¬ p454)) : p444 ∨ p438 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p444) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p438) := fun hu => hn (Or.inr hu)
  have u2 : p453 := by
    rcases h24480 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p445 := by
    rcases h24481 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p446 := by
    rcases h24482 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p447 := by
    rcases h24483 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p448 := by
    rcases h24484 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p449) := by
    rcases h2361 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p450 := by
    rcases h2467 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p451 := by
    rcases h2468 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p452 := by
    rcases h2469 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p454 := by
    rcases h2471 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h2386 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u11)

theorem step24486 (p495 p498 p502 p503 p504 p505 p506 p507 p508 p509 p510 p511 : Prop)
    (h2763 : p495 ∨ p498 ∨ (¬ p507) ∨ (¬ p508) ∨ (¬ p509) ∨ (¬ p510) ∨ (¬ p511))
    (h2831 : p502 ∨ p511)
    (h2836 : p503 ∨ p511)
    (h2841 : p504 ∨ p511)
    (h2846 : p505 ∨ p511)
    (h2851 : p506 ∨ p511)
    (h2738 : p495 ∨ p498 ∨ (¬ p502) ∨ (¬ p503) ∨ (¬ p504) ∨ (¬ p505) ∨ (¬ p506)) : p498 ∨ (¬ p510) ∨ p495 ∨ (¬ p509) ∨ (¬ p507) ∨ (¬ p508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p498) := fun hu => hn (Or.inl hu)
  have u1 : p510 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p509 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p507 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p511) := by
    rcases h2763 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u1)
    · exact q6
  have u7 : p502 := by
    rcases h2831 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p503 := by
    rcases h2836 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p504 := by
    rcases h2841 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p505 := by
    rcases h2846 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p506 := by
    rcases h2851 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h2738 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step24487 (p495 p498 p507 p508 p509 p510 : Prop)
    (h20867 : p507 ∨ p495 ∨ p498)
    (h20868 : p508 ∨ p495 ∨ p498)
    (h20869 : p509 ∨ p495 ∨ p498)
    (h20870 : p510 ∨ p495 ∨ p498)
    (h24486 : p498 ∨ (¬ p510) ∨ p495 ∨ (¬ p509) ∨ (¬ p507) ∨ (¬ p508)) : p498 ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p498) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr hu)
  have u2 : p507 := by
    rcases h20867 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u3 : p508 := by
    rcases h20868 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u4 : p509 := by
    rcases h20869 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u5 : p510 := by
    rcases h20870 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  rcases h24486 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step24490 (p814 p820 p823 p824 p825 p826 p827 p831 : Prop)
    (h4772 : p823 ∨ p831)
    (h4777 : p824 ∨ p831)
    (h4782 : p825 ∨ p831)
    (h4787 : p826 ∨ p831)
    (h4792 : p827 ∨ p831)
    (h4680 : p814 ∨ p820 ∨ (¬ p823) ∨ (¬ p824) ∨ (¬ p825) ∨ (¬ p826) ∨ (¬ p827)) : p831 ∨ p820 ∨ p814 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p831) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p820) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p814) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p823 := by
    rcases h4772 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p824 := by
    rcases h4777 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p825 := by
    rcases h4782 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p826 := by
    rcases h4787 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p827 := by
    rcases h4792 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4680 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24491 (p814 p820 p823 p824 p825 p826 p827 p832 : Prop)
    (h4773 : p823 ∨ p832)
    (h4778 : p824 ∨ p832)
    (h4783 : p825 ∨ p832)
    (h4788 : p826 ∨ p832)
    (h4793 : p827 ∨ p832)
    (h4680 : p814 ∨ p820 ∨ (¬ p823) ∨ (¬ p824) ∨ (¬ p825) ∨ (¬ p826) ∨ (¬ p827)) : p832 ∨ p820 ∨ p814 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p832) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p820) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p814) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p823 := by
    rcases h4773 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p824 := by
    rcases h4778 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p825 := by
    rcases h4783 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p826 := by
    rcases h4788 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p827 := by
    rcases h4793 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4680 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24492 (p814 p820 p823 p824 p825 p826 p827 p828 : Prop)
    (h4769 : p823 ∨ p828)
    (h4774 : p824 ∨ p828)
    (h4779 : p825 ∨ p828)
    (h4784 : p826 ∨ p828)
    (h4789 : p827 ∨ p828)
    (h4680 : p814 ∨ p820 ∨ (¬ p823) ∨ (¬ p824) ∨ (¬ p825) ∨ (¬ p826) ∨ (¬ p827)) : p828 ∨ p820 ∨ p814 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p828) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p820) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p814) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p823 := by
    rcases h4769 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p824 := by
    rcases h4774 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p825 := by
    rcases h4779 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p826 := by
    rcases h4784 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p827 := by
    rcases h4789 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4680 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24493 (p814 p820 p823 p824 p825 p826 p827 p829 : Prop)
    (h4770 : p823 ∨ p829)
    (h4775 : p824 ∨ p829)
    (h4780 : p825 ∨ p829)
    (h4785 : p826 ∨ p829)
    (h4790 : p827 ∨ p829)
    (h4680 : p814 ∨ p820 ∨ (¬ p823) ∨ (¬ p824) ∨ (¬ p825) ∨ (¬ p826) ∨ (¬ p827)) : p829 ∨ p820 ∨ p814 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p829) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p820) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p814) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p823 := by
    rcases h4770 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p824 := by
    rcases h4775 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p825 := by
    rcases h4780 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p826 := by
    rcases h4785 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p827 := by
    rcases h4790 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4680 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24494 (p814 p820 p823 p824 p825 p826 p827 p828 p829 p830 p831 p832 : Prop)
    (h4705 : p814 ∨ p820 ∨ (¬ p828) ∨ (¬ p829) ∨ (¬ p830) ∨ (¬ p831) ∨ (¬ p832))
    (h4771 : p823 ∨ p830)
    (h4776 : p824 ∨ p830)
    (h4781 : p825 ∨ p830)
    (h4786 : p826 ∨ p830)
    (h4791 : p827 ∨ p830)
    (h4680 : p814 ∨ p820 ∨ (¬ p823) ∨ (¬ p824) ∨ (¬ p825) ∨ (¬ p826) ∨ (¬ p827)) : (¬ p829) ∨ (¬ p831) ∨ p814 ∨ p820 ∨ (¬ p828) ∨ (¬ p832) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p829 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p831 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p814) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p820) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p828 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p832 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p830) := by
    rcases h4705 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u0)
    · exact q4
    · exact False.elim (q5 u1)
    · exact False.elim (q6 u5)
  have u7 : p823 := by
    rcases h4771 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p824 := by
    rcases h4776 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p825 := by
    rcases h4781 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p826 := by
    rcases h4786 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p827 := by
    rcases h4791 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h4680 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step24495 (p814 p820 p828 p829 p831 p832 : Prop)
    (h24490 : p831 ∨ p820 ∨ p814)
    (h24491 : p832 ∨ p820 ∨ p814)
    (h24492 : p828 ∨ p820 ∨ p814)
    (h24493 : p829 ∨ p820 ∨ p814)
    (h24494 : (¬ p829) ∨ (¬ p831) ∨ p814 ∨ p820 ∨ (¬ p828) ∨ (¬ p832)) : p820 ∨ p814 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p820) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p814) := fun hu => hn (Or.inr hu)
  have u2 : p831 := by
    rcases h24490 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p832 := by
    rcases h24491 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p828 := by
    rcases h24492 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p829 := by
    rcases h24493 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h24494 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step24496 (p401 p406 p409 p410 p411 p412 p413 p417 : Prop)
    (h2309 : p409 ∨ p417)
    (h2314 : p410 ∨ p417)
    (h2319 : p411 ∨ p417)
    (h2324 : p412 ∨ p417)
    (h2329 : p413 ∨ p417)
    (h2213 : p401 ∨ p406 ∨ (¬ p409) ∨ (¬ p410) ∨ (¬ p411) ∨ (¬ p412) ∨ (¬ p413)) : p417 ∨ p401 ∨ p406 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p417) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p401) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p406) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p409 := by
    rcases h2309 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p410 := by
    rcases h2314 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p411 := by
    rcases h2319 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p412 := by
    rcases h2324 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p413 := by
    rcases h2329 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2213 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24497 (p401 p406 p409 p414 p415 p416 p417 p418 : Prop)
    (h24496 : p417 ∨ p401 ∨ p406)
    (h2306 : p409 ∨ p414)
    (h2307 : p409 ∨ p415)
    (h2308 : p409 ∨ p416)
    (h2310 : p409 ∨ p418)
    (h2238 : p401 ∨ p406 ∨ (¬ p414) ∨ (¬ p415) ∨ (¬ p416) ∨ (¬ p417) ∨ (¬ p418)) : p409 ∨ p401 ∨ p406 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p409) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p401) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p406) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p417 := by
    rcases h24496 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p414 := by
    rcases h2306 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p415 := by
    rcases h2307 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p416 := by
    rcases h2308 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p418 := by
    rcases h2310 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2238 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24498 (p401 p406 p410 p414 p415 p416 p417 p418 : Prop)
    (h24496 : p417 ∨ p401 ∨ p406)
    (h2311 : p410 ∨ p414)
    (h2312 : p410 ∨ p415)
    (h2313 : p410 ∨ p416)
    (h2315 : p410 ∨ p418)
    (h2238 : p401 ∨ p406 ∨ (¬ p414) ∨ (¬ p415) ∨ (¬ p416) ∨ (¬ p417) ∨ (¬ p418)) : p410 ∨ p401 ∨ p406 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p410) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p401) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p406) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p417 := by
    rcases h24496 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p414 := by
    rcases h2311 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p415 := by
    rcases h2312 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p416 := by
    rcases h2313 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p418 := by
    rcases h2315 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2238 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24499 (p401 p406 p411 p414 p415 p416 p417 p418 : Prop)
    (h24496 : p417 ∨ p401 ∨ p406)
    (h2316 : p411 ∨ p414)
    (h2317 : p411 ∨ p415)
    (h2318 : p411 ∨ p416)
    (h2320 : p411 ∨ p418)
    (h2238 : p401 ∨ p406 ∨ (¬ p414) ∨ (¬ p415) ∨ (¬ p416) ∨ (¬ p417) ∨ (¬ p418)) : p411 ∨ p401 ∨ p406 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p411) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p401) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p406) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p417 := by
    rcases h24496 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p414 := by
    rcases h2316 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p415 := by
    rcases h2317 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p416 := by
    rcases h2318 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p418 := by
    rcases h2320 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2238 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24500 (p401 p406 p412 p414 p415 p416 p417 p418 : Prop)
    (h24496 : p417 ∨ p401 ∨ p406)
    (h2321 : p412 ∨ p414)
    (h2322 : p412 ∨ p415)
    (h2323 : p412 ∨ p416)
    (h2325 : p412 ∨ p418)
    (h2238 : p401 ∨ p406 ∨ (¬ p414) ∨ (¬ p415) ∨ (¬ p416) ∨ (¬ p417) ∨ (¬ p418)) : p412 ∨ p401 ∨ p406 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p412) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p401) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p406) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p417 := by
    rcases h24496 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p414 := by
    rcases h2321 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p415 := by
    rcases h2322 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p416 := by
    rcases h2323 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p418 := by
    rcases h2325 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2238 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24501 (p401 p406 p409 p410 p411 p412 p413 p414 p415 p416 p417 p418 : Prop)
    (h24496 : p417 ∨ p401 ∨ p406)
    (h24497 : p409 ∨ p401 ∨ p406)
    (h24498 : p410 ∨ p401 ∨ p406)
    (h24499 : p411 ∨ p401 ∨ p406)
    (h24500 : p412 ∨ p401 ∨ p406)
    (h2213 : p401 ∨ p406 ∨ (¬ p409) ∨ (¬ p410) ∨ (¬ p411) ∨ (¬ p412) ∨ (¬ p413))
    (h2326 : p413 ∨ p414)
    (h2327 : p413 ∨ p415)
    (h2328 : p413 ∨ p416)
    (h2330 : p413 ∨ p418)
    (h2238 : p401 ∨ p406 ∨ (¬ p414) ∨ (¬ p415) ∨ (¬ p416) ∨ (¬ p417) ∨ (¬ p418)) : p401 ∨ p406 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p401) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p406) := fun hu => hn (Or.inr hu)
  have u2 : p417 := by
    rcases h24496 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p409 := by
    rcases h24497 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p410 := by
    rcases h24498 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p411 := by
    rcases h24499 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p412 := by
    rcases h24500 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p413) := by
    rcases h2213 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u0 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p414 := by
    rcases h2326 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p415 := by
    rcases h2327 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p416 := by
    rcases h2328 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p418 := by
    rcases h2330 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h2238 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u11)

theorem step24503 (p1385 p1392 p1396 p1401 p1402 p1403 p1404 p1405 : Prop)
    (h8449 : p1396 ∨ p1401)
    (h8450 : p1396 ∨ p1402)
    (h8451 : p1396 ∨ p1403)
    (h8452 : p1396 ∨ p1404)
    (h8385 : p1385 ∨ p1392 ∨ (¬ p1401) ∨ (¬ p1402) ∨ (¬ p1403) ∨ (¬ p1404) ∨ (¬ p1405)) : p1396 ∨ (¬ p1405) ∨ p1392 ∨ p1385 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1396) := fun hu => hn (Or.inl hu)
  have u1 : p1405 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1392) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1401 := by
    rcases h8449 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1402 := by
    rcases h8450 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1403 := by
    rcases h8451 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1404 := by
    rcases h8452 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8385 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24504 (p1385 p1392 p1397 p1401 p1402 p1403 p1404 p1405 : Prop)
    (h8454 : p1397 ∨ p1401)
    (h8455 : p1397 ∨ p1402)
    (h8456 : p1397 ∨ p1403)
    (h8457 : p1397 ∨ p1404)
    (h8385 : p1385 ∨ p1392 ∨ (¬ p1401) ∨ (¬ p1402) ∨ (¬ p1403) ∨ (¬ p1404) ∨ (¬ p1405)) : p1397 ∨ (¬ p1405) ∨ p1392 ∨ p1385 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1397) := fun hu => hn (Or.inl hu)
  have u1 : p1405 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1392) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1401 := by
    rcases h8454 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1402 := by
    rcases h8455 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1403 := by
    rcases h8456 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1404 := by
    rcases h8457 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8385 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24505 (p1385 p1392 p1398 p1401 p1402 p1403 p1404 p1405 : Prop)
    (h8459 : p1398 ∨ p1401)
    (h8460 : p1398 ∨ p1402)
    (h8461 : p1398 ∨ p1403)
    (h8462 : p1398 ∨ p1404)
    (h8385 : p1385 ∨ p1392 ∨ (¬ p1401) ∨ (¬ p1402) ∨ (¬ p1403) ∨ (¬ p1404) ∨ (¬ p1405)) : p1398 ∨ (¬ p1405) ∨ p1392 ∨ p1385 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1398) := fun hu => hn (Or.inl hu)
  have u1 : p1405 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1392) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1401 := by
    rcases h8459 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1402 := by
    rcases h8460 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1403 := by
    rcases h8461 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1404 := by
    rcases h8462 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8385 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24506 (p1385 p1392 p1399 p1401 p1402 p1403 p1404 p1405 : Prop)
    (h8464 : p1399 ∨ p1401)
    (h8465 : p1399 ∨ p1402)
    (h8466 : p1399 ∨ p1403)
    (h8467 : p1399 ∨ p1404)
    (h8385 : p1385 ∨ p1392 ∨ (¬ p1401) ∨ (¬ p1402) ∨ (¬ p1403) ∨ (¬ p1404) ∨ (¬ p1405)) : p1399 ∨ (¬ p1405) ∨ p1392 ∨ p1385 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1399) := fun hu => hn (Or.inl hu)
  have u1 : p1405 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1392) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1401 := by
    rcases h8464 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1402 := by
    rcases h8465 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1403 := by
    rcases h8466 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1404 := by
    rcases h8467 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8385 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24507 (p1385 p1392 p1396 p1397 p1398 p1399 p1400 p1401 p1402 p1403 p1404 p1405 : Prop)
    (h24503 : p1396 ∨ (¬ p1405) ∨ p1392 ∨ p1385)
    (h24504 : p1397 ∨ (¬ p1405) ∨ p1392 ∨ p1385)
    (h24505 : p1398 ∨ (¬ p1405) ∨ p1392 ∨ p1385)
    (h24506 : p1399 ∨ (¬ p1405) ∨ p1392 ∨ p1385)
    (h8360 : p1385 ∨ p1392 ∨ (¬ p1396) ∨ (¬ p1397) ∨ (¬ p1398) ∨ (¬ p1399) ∨ (¬ p1400))
    (h8469 : p1400 ∨ p1401)
    (h8470 : p1400 ∨ p1402)
    (h8471 : p1400 ∨ p1403)
    (h8472 : p1400 ∨ p1404)
    (h8385 : p1385 ∨ p1392 ∨ (¬ p1401) ∨ (¬ p1402) ∨ (¬ p1403) ∨ (¬ p1404) ∨ (¬ p1405)) : (¬ p1405) ∨ p1392 ∨ p1385 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1405 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1392) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1396 := by
    rcases h24503 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u4 : p1397 := by
    rcases h24504 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u5 : p1398 := by
    rcases h24505 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u6 : p1399 := by
    rcases h24506 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u7 : (¬ p1400) := by
    rcases h8360 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p1401 := by
    rcases h8469 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p1402 := by
    rcases h8470 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p1403 := by
    rcases h8471 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p1404 := by
    rcases h8472 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h8385 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u0)

theorem step24511 (p1 p2 p6 p102 p105 p127 p382 p477 p996 : Prop)
    (h22605 : p127 ∨ p6)
    (h24223 : p6 ∨ (¬ p102) ∨ (¬ p2))
    (h17918 : (¬ p1) ∨ (¬ p105) ∨ (¬ p127) ∨ (¬ p382) ∨ (¬ p477) ∨ (¬ p996))
    (h24233 : p102 ∨ p105) : p6 ∨ (¬ p1) ∨ (¬ p477) ∨ (¬ p2) ∨ (¬ p996) ∨ (¬ p382) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p6) := fun hu => hn (Or.inl hu)
  have u1 : p1 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p477 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p127 := by
    rcases h22605 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : (¬ p102) := by
    rcases h24223 with q0 | q1 | q2
    · exact False.elim (u0 q0)
    · exact q1
    · exact False.elim (q2 u3)
  have u8 : (¬ p105) := by
    rcases h17918 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u1)
    · exact q1
    · exact False.elim (q2 u6)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u2)
    · exact False.elim (q5 u4)
  rcases h24233 with q0 | q1
  · exact False.elim (u7 q0)
  · exact False.elim (u8 q1)

theorem step24516 (p10 p323 p325 p329 p331 p381 p384 p387 p996 p1206 : Prop)
    (h19462 : p331 ∨ (¬ p387))
    (h20914 : p387 ∨ p381)
    (h24334 : p384 ∨ p387)
    (h13045 : (¬ p325) ∨ p387 ∨ (¬ p996))
    (h22236 : p331 ∨ p325 ∨ p10)
    (h1698 : (¬ p10) ∨ (¬ p323))
    (h13849 : (¬ p10) ∨ (¬ p381) ∨ p1206)
    (h21607 : p329 ∨ p323 ∨ p325)
    (h13036 : (¬ p329) ∨ (¬ p384) ∨ (¬ p996) ∨ (¬ p1206)) : p331 ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p331) := fun hu => hn (Or.inl hu)
  have u1 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p387) := by
    rcases h19462 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p381 := by
    rcases h20914 with q0 | q1
    · exact False.elim (u2 q0)
    · exact q1
  have u4 : p384 := by
    rcases h24334 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : (¬ p325) := by
    rcases h13045 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u1)
  have u6 : p10 := by
    rcases h22236 with q0 | q1 | q2
    · exact False.elim (u0 q0)
    · exact False.elim (u5 q1)
    · exact q2
  have u7 : (¬ p323) := by
    rcases h1698 with q0 | q1
    · exact False.elim (q0 u6)
    · exact q1
  have u8 : p1206 := by
    rcases h13849 with q0 | q1 | q2
    · exact False.elim (q0 u6)
    · exact False.elim (q1 u3)
    · exact q2
  have u9 : p329 := by
    rcases h21607 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u7 q1)
    · exact False.elim (u5 q2)
  rcases h13036 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u8)

theorem step24517 (p10 p323 p325 p329 p381 p384 p387 p996 p1206 : Prop)
    (h13045 : (¬ p325) ∨ p387 ∨ (¬ p996))
    (h24334 : p384 ∨ p387)
    (h20914 : p387 ∨ p381)
    (h1698 : (¬ p10) ∨ (¬ p323))
    (h13849 : (¬ p10) ∨ (¬ p381) ∨ p1206)
    (h21607 : p329 ∨ p323 ∨ p325)
    (h13036 : (¬ p329) ∨ (¬ p384) ∨ (¬ p996) ∨ (¬ p1206)) : (¬ p10) ∨ p387 ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p387) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p325) := by
    rcases h13045 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u2)
  have u4 : p384 := by
    rcases h24334 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p381 := by
    rcases h20914 with q0 | q1
    · exact False.elim (u1 q0)
    · exact q1
  have u6 : (¬ p323) := by
    rcases h1698 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u7 : p1206 := by
    rcases h13849 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact False.elim (q1 u5)
    · exact q2
  have u8 : p329 := by
    rcases h21607 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u6 q1)
    · exact False.elim (u3 q2)
  rcases h13036 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u7)

theorem step24518 (p10 p11 p17 p121 p126 p237 p256 p258 p261 p265 p283 p286 p288 p289 p303 p329 p331 p384 p387 p961 p996 p1080 p1206 p1443 : Prop)
    (h24334 : p384 ∨ p387)
    (h24517 : (¬ p10) ∨ p387 ∨ (¬ p996))
    (h21610 : p329 ∨ p10)
    (h13036 : (¬ p329) ∨ (¬ p384) ∨ (¬ p996) ∨ (¬ p1206))
    (h21134 : p121 ∨ p1206)
    (h18529 : (¬ p121) ∨ p1080)
    (h21394 : p387 ∨ p303)
    (h22213 : p126 ∨ (¬ p303) ∨ (¬ p996) ∨ p10)
    (h24516 : p331 ∨ (¬ p996))
    (h16600 : (¬ p126) ∨ (¬ p265) ∨ (¬ p331) ∨ (¬ p384) ∨ (¬ p961) ∨ (¬ p996))
    (h21151 : p17 ∨ p265)
    (h10652 : (¬ p17) ∨ (¬ p256))
    (h8758 : (¬ p17) ∨ (¬ p237) ∨ (¬ p283))
    (h22105 : p261 ∨ p256)
    (h21864 : p283 ∨ p288)
    (h9406 : (¬ p258) ∨ (¬ p288))
    (h21140 : p286 ∨ p258)
    (h21145 : p289 ∨ p283 ∨ p258)
    (h20299 : (¬ p11) ∨ (¬ p17) ∨ (¬ p237) ∨ (¬ p286) ∨ (¬ p1080))
    (h18302 : (¬ p237) ∨ (¬ p261) ∨ (¬ p289) ∨ (¬ p961) ∨ (¬ p1443))
    (h21227 : p1443 ∨ p11) : (¬ p961) ∨ p387 ∨ (¬ p237) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p387) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p384 := by
    rcases h24334 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : (¬ p10) := by
    rcases h24517 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u3)
  have u6 : p329 := by
    rcases h21610 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u7 : (¬ p1206) := by
    rcases h13036 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u6)
    · exact False.elim (q1 u4)
    · exact False.elim (q2 u3)
    · exact q3
  have u8 : p121 := by
    rcases h21134 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p1080 := by
    rcases h18529 with q0 | q1
    · exact False.elim (q0 u8)
    · exact q1
  have u10 : p303 := by
    rcases h21394 with q0 | q1
    · exact False.elim (u1 q0)
    · exact q1
  have u11 : p126 := by
    rcases h22213 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u10)
    · exact False.elim (q2 u3)
    · exact False.elim (u5 q3)
  have u12 : p331 := by
    rcases h24516 with q0 | q1
    · exact q0
    · exact False.elim (q1 u3)
  have u13 : (¬ p265) := by
    rcases h16600 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u11)
    · exact q1
    · exact False.elim (q2 u12)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u3)
  have u14 : p17 := by
    rcases h21151 with q0 | q1
    · exact q0
    · exact False.elim (u13 q1)
  have u15 : (¬ p256) := by
    rcases h10652 with q0 | q1
    · exact False.elim (q0 u14)
    · exact q1
  have u16 : (¬ p283) := by
    rcases h8758 with q0 | q1 | q2
    · exact False.elim (q0 u14)
    · exact False.elim (q1 u2)
    · exact q2
  have u17 : p261 := by
    rcases h22105 with q0 | q1
    · exact q0
    · exact False.elim (u15 q1)
  have u18 : p288 := by
    rcases h21864 with q0 | q1
    · exact False.elim (u16 q0)
    · exact q1
  have u19 : (¬ p258) := by
    rcases h9406 with q0 | q1
    · exact q0
    · exact False.elim (q1 u18)
  have u20 : p286 := by
    rcases h21140 with q0 | q1
    · exact q0
    · exact False.elim (u19 q1)
  have u21 : p289 := by
    rcases h21145 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u16 q1)
    · exact False.elim (u19 q2)
  have u22 : (¬ p11) := by
    rcases h20299 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u14)
    · exact False.elim (q2 u2)
    · exact False.elim (q3 u20)
    · exact False.elim (q4 u9)
  have u23 : (¬ p1443) := by
    rcases h18302 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u2)
    · exact False.elim (q1 u17)
    · exact False.elim (q2 u21)
    · exact False.elim (q3 u0)
    · exact q4
  rcases h21227 with q0 | q1
  · exact False.elim (u23 q0)
  · exact False.elim (u22 q1)

theorem step24519 (p17 p63 p83 p85 p88 p89 p256 p261 p495 p498 p499 p575 p581 p922 p929 p1096 : Prop)
    (h10652 : (¬ p17) ∨ (¬ p256))
    (h22105 : p261 ∨ p256)
    (h9344 : (¬ p495) ∨ (¬ p499))
    (h24487 : p498 ∨ p495)
    (h13480 : p89 ∨ (¬ p261) ∨ (¬ p498))
    (h645 : (¬ p63) ∨ (¬ p85))
    (h8759 : (¬ p85) ∨ (¬ p922) ∨ (¬ p1096))
    (h9356 : (¬ p85) ∨ (¬ p499) ∨ (¬ p575))
    (h14053 : (¬ p85) ∨ (¬ p88) ∨ (¬ p89))
    (h22864 : p929 ∨ p922)
    (h23624 : p575 ∨ p581)
    (h23700 : p83 ∨ p88 ∨ p63)
    (h16620 : (¬ p17) ∨ (¬ p83) ∨ (¬ p581) ∨ (¬ p929) ∨ (¬ p1096)) : (¬ p85) ∨ (¬ p1096) ∨ (¬ p499) ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p256) := by
    rcases h10652 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  have u5 : p261 := by
    rcases h22105 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u6 : (¬ p495) := by
    rcases h9344 with q0 | q1
    · exact q0
    · exact False.elim (q1 u2)
  have u7 : p498 := by
    rcases h24487 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p89 := by
    rcases h13480 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u5)
    · exact False.elim (q2 u7)
  have u9 : (¬ p63) := by
    rcases h645 with q0 | q1
    · exact q0
    · exact False.elim (q1 u0)
  have u10 : (¬ p922) := by
    rcases h8759 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (q2 u1)
  have u11 : (¬ p575) := by
    rcases h9356 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact False.elim (q1 u2)
    · exact q2
  have u12 : (¬ p88) := by
    rcases h14053 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (q2 u8)
  have u13 : p929 := by
    rcases h22864 with q0 | q1
    · exact q0
    · exact False.elim (u10 q1)
  have u14 : p581 := by
    rcases h23624 with q0 | q1
    · exact False.elim (u11 q0)
    · exact q1
  have u15 : p83 := by
    rcases h23700 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u12 q1)
    · exact False.elim (u9 q2)
  rcases h16620 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u15)
  · exact False.elim (q2 u14)
  · exact False.elim (q3 u13)
  · exact False.elim (q4 u1)

theorem step24520 (p1 p104 p110 p224 p225 p344 p346 p540 p544 p657 p996 : Prop)
    (h22560 : p346 ∨ p344)
    (h20814 : p224 ∨ p657)
    (h13059 : (¬ p540) ∨ p657 ∨ (¬ p996))
    (h21071 : p540 ∨ p544)
    (h11784 : (¬ p225) ∨ (¬ p544))
    (h13591 : (¬ p104) ∨ p344 ∨ (¬ p544))
    (h21617 : p1 ∨ p225)
    (h22241 : p110 ∨ p104)
    (h17153 : (¬ p1) ∨ (¬ p110) ∨ (¬ p224) ∨ (¬ p346) ∨ (¬ p996)) : p657 ∨ p344 ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p657) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p346 := by
    rcases h22560 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u4 : p224 := by
    rcases h20814 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : (¬ p540) := by
    rcases h13059 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u2)
  have u6 : p544 := by
    rcases h21071 with q0 | q1
    · exact False.elim (u5 q0)
    · exact q1
  have u7 : (¬ p225) := by
    rcases h11784 with q0 | q1
    · exact q0
    · exact False.elim (q1 u6)
  have u8 : (¬ p104) := by
    rcases h13591 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u6)
  have u9 : p1 := by
    rcases h21617 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p110 := by
    rcases h22241 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h17153 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)

theorem step24521 (p104 p110 p225 p303 p345 p346 p544 p657 : Prop)
    (h22947 : p544 ∨ p225)
    (h14153 : (¬ p104) ∨ p225 ∨ (¬ p346))
    (h18093 : (¬ p110) ∨ (¬ p303) ∨ (¬ p345) ∨ (¬ p544) ∨ (¬ p657))
    (h22241 : p110 ∨ p104) : p225 ∨ (¬ p657) ∨ (¬ p346) ∨ (¬ p345) ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p225) := fun hu => hn (Or.inl hu)
  have u1 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p346 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p544 := by
    rcases h22947 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : (¬ p104) := by
    rcases h14153 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u2)
  have u7 : (¬ p110) := by
    rcases h18093 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u4)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
  rcases h22241 with q0 | q1
  · exact False.elim (u7 q0)
  · exact False.elim (u6 q1)

theorem step24522 (p814 p821 p823 p828 p829 p830 p831 p832 : Prop)
    (h4769 : p823 ∨ p828)
    (h4770 : p823 ∨ p829)
    (h4771 : p823 ∨ p830)
    (h4772 : p823 ∨ p831)
    (h4773 : p823 ∨ p832)
    (h4707 : p814 ∨ p821 ∨ (¬ p828) ∨ (¬ p829) ∨ (¬ p830) ∨ (¬ p831) ∨ (¬ p832)) : p823 ∨ p821 ∨ p814 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p823) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p821) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p814) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p828 := by
    rcases h4769 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p829 := by
    rcases h4770 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p830 := by
    rcases h4771 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p831 := by
    rcases h4772 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p832 := by
    rcases h4773 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4707 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24523 (p814 p821 p824 p828 p829 p830 p831 p832 : Prop)
    (h4774 : p824 ∨ p828)
    (h4775 : p824 ∨ p829)
    (h4776 : p824 ∨ p830)
    (h4777 : p824 ∨ p831)
    (h4778 : p824 ∨ p832)
    (h4707 : p814 ∨ p821 ∨ (¬ p828) ∨ (¬ p829) ∨ (¬ p830) ∨ (¬ p831) ∨ (¬ p832)) : p824 ∨ p821 ∨ p814 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p824) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p821) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p814) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p828 := by
    rcases h4774 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p829 := by
    rcases h4775 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p830 := by
    rcases h4776 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p831 := by
    rcases h4777 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p832 := by
    rcases h4778 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4707 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24524 (p814 p821 p825 p828 p829 p830 p831 p832 : Prop)
    (h4779 : p825 ∨ p828)
    (h4780 : p825 ∨ p829)
    (h4781 : p825 ∨ p830)
    (h4782 : p825 ∨ p831)
    (h4783 : p825 ∨ p832)
    (h4707 : p814 ∨ p821 ∨ (¬ p828) ∨ (¬ p829) ∨ (¬ p830) ∨ (¬ p831) ∨ (¬ p832)) : p825 ∨ p821 ∨ p814 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p825) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p821) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p814) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p828 := by
    rcases h4779 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p829 := by
    rcases h4780 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p830 := by
    rcases h4781 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p831 := by
    rcases h4782 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p832 := by
    rcases h4783 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4707 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24525 (p814 p821 p826 p828 p829 p830 p831 p832 : Prop)
    (h4784 : p826 ∨ p828)
    (h4785 : p826 ∨ p829)
    (h4786 : p826 ∨ p830)
    (h4787 : p826 ∨ p831)
    (h4788 : p826 ∨ p832)
    (h4707 : p814 ∨ p821 ∨ (¬ p828) ∨ (¬ p829) ∨ (¬ p830) ∨ (¬ p831) ∨ (¬ p832)) : p826 ∨ p821 ∨ p814 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p826) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p821) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p814) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p828 := by
    rcases h4784 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p829 := by
    rcases h4785 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p830 := by
    rcases h4786 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p831 := by
    rcases h4787 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p832 := by
    rcases h4788 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4707 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24526 (p814 p821 p823 p824 p825 p826 p827 p828 p829 p830 p831 p832 : Prop)
    (h4682 : p814 ∨ p821 ∨ (¬ p823) ∨ (¬ p824) ∨ (¬ p825) ∨ (¬ p826) ∨ (¬ p827))
    (h4789 : p827 ∨ p828)
    (h4790 : p827 ∨ p829)
    (h4791 : p827 ∨ p830)
    (h4792 : p827 ∨ p831)
    (h4793 : p827 ∨ p832)
    (h4707 : p814 ∨ p821 ∨ (¬ p828) ∨ (¬ p829) ∨ (¬ p830) ∨ (¬ p831) ∨ (¬ p832)) : (¬ p826) ∨ (¬ p823) ∨ p814 ∨ (¬ p824) ∨ p821 ∨ (¬ p825) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p826 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p823 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p814) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p824 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p821) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p825 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p827) := by
    rcases h4682 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u4 q1)
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u3)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p828 := by
    rcases h4789 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p829 := by
    rcases h4790 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p830 := by
    rcases h4791 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p831 := by
    rcases h4792 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p832 := by
    rcases h4793 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h4707 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step24527 (p814 p821 p823 p824 p825 p826 : Prop)
    (h24522 : p823 ∨ p821 ∨ p814)
    (h24523 : p824 ∨ p821 ∨ p814)
    (h24524 : p825 ∨ p821 ∨ p814)
    (h24525 : p826 ∨ p821 ∨ p814)
    (h24526 : (¬ p826) ∨ (¬ p823) ∨ p814 ∨ (¬ p824) ∨ p821 ∨ (¬ p825)) : p821 ∨ p814 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p821) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p814) := fun hu => hn (Or.inr hu)
  have u2 : p823 := by
    rcases h24522 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p824 := by
    rcases h24523 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p825 := by
    rcases h24524 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p826 := by
    rcases h24525 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h24526 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (u0 q4)
  · exact False.elim (q5 u4)

theorem step24528 (p899 p904 p907 p912 p913 p914 p915 p916 : Prop)
    (h5301 : p907 ∨ p912)
    (h5302 : p907 ∨ p913)
    (h5303 : p907 ∨ p914)
    (h5305 : p907 ∨ p916)
    (h5233 : p899 ∨ p904 ∨ (¬ p912) ∨ (¬ p913) ∨ (¬ p914) ∨ (¬ p915) ∨ (¬ p916)) : p907 ∨ (¬ p915) ∨ p899 ∨ p904 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p907) := fun hu => hn (Or.inl hu)
  have u1 : p915 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p899) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p904) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p912 := by
    rcases h5301 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p913 := by
    rcases h5302 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p914 := by
    rcases h5303 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p916 := by
    rcases h5305 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5233 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step24529 (p899 p904 p908 p912 p913 p914 p915 p916 : Prop)
    (h5306 : p908 ∨ p912)
    (h5307 : p908 ∨ p913)
    (h5308 : p908 ∨ p914)
    (h5310 : p908 ∨ p916)
    (h5233 : p899 ∨ p904 ∨ (¬ p912) ∨ (¬ p913) ∨ (¬ p914) ∨ (¬ p915) ∨ (¬ p916)) : p908 ∨ (¬ p915) ∨ p899 ∨ p904 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p908) := fun hu => hn (Or.inl hu)
  have u1 : p915 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p899) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p904) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p912 := by
    rcases h5306 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p913 := by
    rcases h5307 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p914 := by
    rcases h5308 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p916 := by
    rcases h5310 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5233 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step24530 (p899 p904 p909 p912 p913 p914 p915 p916 : Prop)
    (h5311 : p909 ∨ p912)
    (h5312 : p909 ∨ p913)
    (h5313 : p909 ∨ p914)
    (h5315 : p909 ∨ p916)
    (h5233 : p899 ∨ p904 ∨ (¬ p912) ∨ (¬ p913) ∨ (¬ p914) ∨ (¬ p915) ∨ (¬ p916)) : p909 ∨ (¬ p915) ∨ p899 ∨ p904 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p909) := fun hu => hn (Or.inl hu)
  have u1 : p915 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p899) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p904) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p912 := by
    rcases h5311 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p913 := by
    rcases h5312 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p914 := by
    rcases h5313 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p916 := by
    rcases h5315 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5233 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step24531 (p899 p904 p910 p912 p913 p914 p915 p916 : Prop)
    (h5316 : p910 ∨ p912)
    (h5317 : p910 ∨ p913)
    (h5318 : p910 ∨ p914)
    (h5320 : p910 ∨ p916)
    (h5233 : p899 ∨ p904 ∨ (¬ p912) ∨ (¬ p913) ∨ (¬ p914) ∨ (¬ p915) ∨ (¬ p916)) : p910 ∨ (¬ p915) ∨ p899 ∨ p904 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p910) := fun hu => hn (Or.inl hu)
  have u1 : p915 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p899) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p904) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p912 := by
    rcases h5316 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p913 := by
    rcases h5317 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p914 := by
    rcases h5318 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p916 := by
    rcases h5320 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5233 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step24534 (p419 p1002 p1009 p1010 p1011 p1012 p1013 p1014 : Prop)
    (h5958 : p1009 ∨ p1010)
    (h5959 : p1009 ∨ p1011)
    (h5961 : p1009 ∨ p1013)
    (h5962 : p1009 ∨ p1014)
    (h5874 : p419 ∨ p1002 ∨ (¬ p1010) ∨ (¬ p1011) ∨ (¬ p1012) ∨ (¬ p1013) ∨ (¬ p1014)) : p1009 ∨ (¬ p1012) ∨ p1002 ∨ p419 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1009) := fun hu => hn (Or.inl hu)
  have u1 : p1012 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1002) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1010 := by
    rcases h5958 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1011 := by
    rcases h5959 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1013 := by
    rcases h5961 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1014 := by
    rcases h5962 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5874 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24535 (p419 p1002 p1005 p1006 p1007 p1008 p1009 p1013 : Prop)
    (h5941 : p1005 ∨ p1013)
    (h5946 : p1006 ∨ p1013)
    (h5951 : p1007 ∨ p1013)
    (h5956 : p1008 ∨ p1013)
    (h5849 : p419 ∨ p1002 ∨ (¬ p1005) ∨ (¬ p1006) ∨ (¬ p1007) ∨ (¬ p1008) ∨ (¬ p1009)) : p1013 ∨ (¬ p1009) ∨ p1002 ∨ p419 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1013) := fun hu => hn (Or.inl hu)
  have u1 : p1009 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1002) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1005 := by
    rcases h5941 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1006 := by
    rcases h5946 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1007 := by
    rcases h5951 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1008 := by
    rcases h5956 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5849 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24536 (p419 p1002 p1005 p1006 p1007 p1008 p1009 p1014 : Prop)
    (h5942 : p1005 ∨ p1014)
    (h5947 : p1006 ∨ p1014)
    (h5952 : p1007 ∨ p1014)
    (h5957 : p1008 ∨ p1014)
    (h5849 : p419 ∨ p1002 ∨ (¬ p1005) ∨ (¬ p1006) ∨ (¬ p1007) ∨ (¬ p1008) ∨ (¬ p1009)) : p1014 ∨ (¬ p1009) ∨ p1002 ∨ p419 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1014) := fun hu => hn (Or.inl hu)
  have u1 : p1009 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1002) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1005 := by
    rcases h5942 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1006 := by
    rcases h5947 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1007 := by
    rcases h5952 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1008 := by
    rcases h5957 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5849 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24537 (p419 p1002 p1005 p1006 p1007 p1008 p1009 p1010 : Prop)
    (h5938 : p1005 ∨ p1010)
    (h5943 : p1006 ∨ p1010)
    (h5948 : p1007 ∨ p1010)
    (h5953 : p1008 ∨ p1010)
    (h5849 : p419 ∨ p1002 ∨ (¬ p1005) ∨ (¬ p1006) ∨ (¬ p1007) ∨ (¬ p1008) ∨ (¬ p1009)) : p1010 ∨ (¬ p1009) ∨ p1002 ∨ p419 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1010) := fun hu => hn (Or.inl hu)
  have u1 : p1009 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1002) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1005 := by
    rcases h5938 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1006 := by
    rcases h5943 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1007 := by
    rcases h5948 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1008 := by
    rcases h5953 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5849 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24538 (p419 p1002 p1005 p1006 p1007 p1008 p1009 p1010 p1011 p1012 p1013 p1014 : Prop)
    (h24534 : p1009 ∨ (¬ p1012) ∨ p1002 ∨ p419)
    (h24535 : p1013 ∨ (¬ p1009) ∨ p1002 ∨ p419)
    (h24536 : p1014 ∨ (¬ p1009) ∨ p1002 ∨ p419)
    (h24537 : p1010 ∨ (¬ p1009) ∨ p1002 ∨ p419)
    (h5874 : p419 ∨ p1002 ∨ (¬ p1010) ∨ (¬ p1011) ∨ (¬ p1012) ∨ (¬ p1013) ∨ (¬ p1014))
    (h5939 : p1005 ∨ p1011)
    (h5944 : p1006 ∨ p1011)
    (h5949 : p1007 ∨ p1011)
    (h5954 : p1008 ∨ p1011)
    (h5849 : p419 ∨ p1002 ∨ (¬ p1005) ∨ (¬ p1006) ∨ (¬ p1007) ∨ (¬ p1008) ∨ (¬ p1009)) : (¬ p1012) ∨ p1002 ∨ p419 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1012 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1002) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p419) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1009 := by
    rcases h24534 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u4 : p1013 := by
    rcases h24535 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u5 : p1014 := by
    rcases h24536 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u6 : p1010 := by
    rcases h24537 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u7 : (¬ p1011) := by
    rcases h5874 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u6)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u5)
  have u8 : p1005 := by
    rcases h5939 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p1006 := by
    rcases h5944 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p1007 := by
    rcases h5949 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p1008 := by
    rcases h5954 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h5849 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u3)

theorem step24539 (p419 p1002 p1005 p1006 p1007 p1008 p1009 p1012 : Prop)
    (h24538 : (¬ p1012) ∨ p1002 ∨ p419)
    (h5940 : p1005 ∨ p1012)
    (h5945 : p1006 ∨ p1012)
    (h5950 : p1007 ∨ p1012)
    (h5955 : p1008 ∨ p1012)
    (h5960 : p1009 ∨ p1012)
    (h5849 : p419 ∨ p1002 ∨ (¬ p1005) ∨ (¬ p1006) ∨ (¬ p1007) ∨ (¬ p1008) ∨ (¬ p1009)) : p1002 ∨ p419 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1002) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p419) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p1012) := by
    rcases h24538 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1005 := by
    rcases h5940 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : p1006 := by
    rcases h5945 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p1007 := by
    rcases h5950 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p1008 := by
    rcases h5955 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p1009 := by
    rcases h5960 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h5849 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24540 (p636 p639 p646 p648 p649 p650 p651 p652 : Prop)
    (h3731 : p646 ∨ p648)
    (h3732 : p646 ∨ p649)
    (h3733 : p646 ∨ p650)
    (h3734 : p646 ∨ p651)
    (h3735 : p646 ∨ p652)
    (h3651 : p636 ∨ p639 ∨ (¬ p648) ∨ (¬ p649) ∨ (¬ p650) ∨ (¬ p651) ∨ (¬ p652)) : p646 ∨ p639 ∨ p636 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p646) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p639) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p636) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p648 := by
    rcases h3731 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p649 := by
    rcases h3732 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p650 := by
    rcases h3733 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p651 := by
    rcases h3734 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p652 := by
    rcases h3735 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3651 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24541 (p636 p639 p643 p644 p645 p646 p647 p648 p649 p650 p651 p652 : Prop)
    (h24540 : p646 ∨ p639 ∨ p636)
    (h24381 : p647 ∨ (¬ p651) ∨ p636 ∨ p639)
    (h24382 : p643 ∨ (¬ p651) ∨ p636 ∨ p639)
    (h24383 : p644 ∨ (¬ p651) ∨ p636 ∨ p639)
    (h3626 : p636 ∨ p639 ∨ (¬ p643) ∨ (¬ p644) ∨ (¬ p645) ∨ (¬ p646) ∨ (¬ p647))
    (h3726 : p645 ∨ p648)
    (h3727 : p645 ∨ p649)
    (h3728 : p645 ∨ p650)
    (h3730 : p645 ∨ p652)
    (h3651 : p636 ∨ p639 ∨ (¬ p648) ∨ (¬ p649) ∨ (¬ p650) ∨ (¬ p651) ∨ (¬ p652)) : (¬ p651) ∨ p639 ∨ p636 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p651 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p639) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p636) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p646 := by
    rcases h24540 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p647 := by
    rcases h24381 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u2 q2)
    · exact False.elim (u1 q3)
  have u5 : p643 := by
    rcases h24382 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u2 q2)
    · exact False.elim (u1 q3)
  have u6 : p644 := by
    rcases h24383 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u2 q2)
    · exact False.elim (u1 q3)
  have u7 : (¬ p645) := by
    rcases h3626 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u6)
    · exact q4
    · exact False.elim (q5 u3)
    · exact False.elim (q6 u4)
  have u8 : p648 := by
    rcases h3726 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p649 := by
    rcases h3727 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p650 := by
    rcases h3728 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p652 := by
    rcases h3730 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h3651 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u11)

theorem step24542 (p636 p639 p643 p644 p645 p646 p647 p651 : Prop)
    (h24540 : p646 ∨ p639 ∨ p636)
    (h24541 : (¬ p651) ∨ p639 ∨ p636)
    (h3719 : p643 ∨ p651)
    (h3724 : p644 ∨ p651)
    (h3729 : p645 ∨ p651)
    (h3739 : p647 ∨ p651)
    (h3626 : p636 ∨ p639 ∨ (¬ p643) ∨ (¬ p644) ∨ (¬ p645) ∨ (¬ p646) ∨ (¬ p647)) : p639 ∨ p636 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p639) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p636) := fun hu => hn (Or.inr hu)
  have u2 : p646 := by
    rcases h24540 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : (¬ p651) := by
    rcases h24541 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p643 := by
    rcases h3719 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u5 : p644 := by
    rcases h3724 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p645 := by
    rcases h3729 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p647 := by
    rcases h3739 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h3626 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u7)

theorem step24543 (p101 p107 p114 p116 p117 p118 p119 p120 : Prop)
    (h635 : p114 ∨ p116)
    (h636 : p114 ∨ p117)
    (h637 : p114 ∨ p118)
    (h638 : p114 ∨ p119)
    (h555 : p101 ∨ p107 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p114 ∨ (¬ p120) ∨ p107 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p114) := fun hu => hn (Or.inl hu)
  have u1 : p120 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p107) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p116 := by
    rcases h635 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p117 := by
    rcases h636 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p118 := by
    rcases h637 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p119 := by
    rcases h638 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h555 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24544 (p101 p107 p111 p112 p113 p114 p115 p116 : Prop)
    (h620 : p111 ∨ p116)
    (h625 : p112 ∨ p116)
    (h630 : p113 ∨ p116)
    (h640 : p115 ∨ p116)
    (h530 : p101 ∨ p107 ∨ (¬ p111) ∨ (¬ p112) ∨ (¬ p113) ∨ (¬ p114) ∨ (¬ p115)) : p116 ∨ (¬ p114) ∨ p107 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p116) := fun hu => hn (Or.inl hu)
  have u1 : p114 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p107) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p111 := by
    rcases h620 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p112 := by
    rcases h625 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p113 := by
    rcases h630 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p115 := by
    rcases h640 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h530 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step24545 (p101 p107 p111 p112 p113 p114 p115 p117 : Prop)
    (h621 : p111 ∨ p117)
    (h626 : p112 ∨ p117)
    (h631 : p113 ∨ p117)
    (h641 : p115 ∨ p117)
    (h530 : p101 ∨ p107 ∨ (¬ p111) ∨ (¬ p112) ∨ (¬ p113) ∨ (¬ p114) ∨ (¬ p115)) : p117 ∨ (¬ p114) ∨ p107 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p117) := fun hu => hn (Or.inl hu)
  have u1 : p114 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p107) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p111 := by
    rcases h621 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p112 := by
    rcases h626 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p113 := by
    rcases h631 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p115 := by
    rcases h641 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h530 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step24546 (p101 p107 p111 p112 p113 p114 p115 p118 : Prop)
    (h622 : p111 ∨ p118)
    (h627 : p112 ∨ p118)
    (h632 : p113 ∨ p118)
    (h642 : p115 ∨ p118)
    (h530 : p101 ∨ p107 ∨ (¬ p111) ∨ (¬ p112) ∨ (¬ p113) ∨ (¬ p114) ∨ (¬ p115)) : p118 ∨ (¬ p114) ∨ p107 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p118) := fun hu => hn (Or.inl hu)
  have u1 : p114 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p107) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p111 := by
    rcases h622 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p112 := by
    rcases h627 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p113 := by
    rcases h632 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p115 := by
    rcases h642 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h530 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step24547 (p101 p107 p111 p112 p113 p114 p115 p116 p117 p118 p119 p120 : Prop)
    (h24543 : p114 ∨ (¬ p120) ∨ p107 ∨ p101)
    (h24544 : p116 ∨ (¬ p114) ∨ p107 ∨ p101)
    (h24545 : p117 ∨ (¬ p114) ∨ p107 ∨ p101)
    (h24546 : p118 ∨ (¬ p114) ∨ p107 ∨ p101)
    (h555 : p101 ∨ p107 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120))
    (h623 : p111 ∨ p119)
    (h628 : p112 ∨ p119)
    (h633 : p113 ∨ p119)
    (h643 : p115 ∨ p119)
    (h530 : p101 ∨ p107 ∨ (¬ p111) ∨ (¬ p112) ∨ (¬ p113) ∨ (¬ p114) ∨ (¬ p115)) : (¬ p120) ∨ p107 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p120 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p107) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p114 := by
    rcases h24543 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u4 : p116 := by
    rcases h24544 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u5 : p117 := by
    rcases h24545 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u6 : p118 := by
    rcases h24546 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u7 : (¬ p119) := by
    rcases h555 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u6)
    · exact q5
    · exact False.elim (q6 u0)
  have u8 : p111 := by
    rcases h623 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p112 := by
    rcases h628 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p113 := by
    rcases h633 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p115 := by
    rcases h643 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h530 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u11)

theorem step24548 (p101 p107 p111 p112 p113 p114 p115 p120 : Prop)
    (h24547 : (¬ p120) ∨ p107 ∨ p101)
    (h624 : p111 ∨ p120)
    (h629 : p112 ∨ p120)
    (h634 : p113 ∨ p120)
    (h639 : p114 ∨ p120)
    (h644 : p115 ∨ p120)
    (h530 : p101 ∨ p107 ∨ (¬ p111) ∨ (¬ p112) ∨ (¬ p113) ∨ (¬ p114) ∨ (¬ p115)) : p107 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p107) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p101) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p120) := by
    rcases h24547 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p111 := by
    rcases h624 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : p112 := by
    rcases h629 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p113 := by
    rcases h634 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p114 := by
    rcases h639 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p115 := by
    rcases h644 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h530 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24549 (p234 p1191 p1197 p1201 p1202 p1203 p1204 p1205 : Prop)
    (h7168 : p1197 ∨ p1201)
    (h7169 : p1197 ∨ p1202)
    (h7170 : p1197 ∨ p1203)
    (h7171 : p1197 ∨ p1204)
    (h7172 : p1197 ∨ p1205)
    (h7110 : p234 ∨ p1191 ∨ (¬ p1201) ∨ (¬ p1202) ∨ (¬ p1203) ∨ (¬ p1204) ∨ (¬ p1205)) : p1197 ∨ p1191 ∨ p234 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1197) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1191) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p234) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1201 := by
    rcases h7168 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1202 := by
    rcases h7169 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1203 := by
    rcases h7170 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1204 := by
    rcases h7171 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1205 := by
    rcases h7172 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7110 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24550 (p234 p1191 p1196 p1197 p1198 p1199 p1200 p1205 : Prop)
    (h24549 : p1197 ∨ p1191 ∨ p234)
    (h7167 : p1196 ∨ p1205)
    (h7177 : p1198 ∨ p1205)
    (h7182 : p1199 ∨ p1205)
    (h7187 : p1200 ∨ p1205)
    (h7085 : p234 ∨ p1191 ∨ (¬ p1196) ∨ (¬ p1197) ∨ (¬ p1198) ∨ (¬ p1199) ∨ (¬ p1200)) : p1205 ∨ p1191 ∨ p234 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1205) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1191) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p234) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1197 := by
    rcases h24549 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1196 := by
    rcases h7167 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1198 := by
    rcases h7177 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1199 := by
    rcases h7182 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1200 := by
    rcases h7187 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7085 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24551 (p234 p1191 p1196 p1197 p1198 p1199 p1200 p1201 : Prop)
    (h24549 : p1197 ∨ p1191 ∨ p234)
    (h7163 : p1196 ∨ p1201)
    (h7173 : p1198 ∨ p1201)
    (h7178 : p1199 ∨ p1201)
    (h7183 : p1200 ∨ p1201)
    (h7085 : p234 ∨ p1191 ∨ (¬ p1196) ∨ (¬ p1197) ∨ (¬ p1198) ∨ (¬ p1199) ∨ (¬ p1200)) : p1201 ∨ p1191 ∨ p234 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1201) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1191) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p234) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1197 := by
    rcases h24549 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1196 := by
    rcases h7163 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1198 := by
    rcases h7173 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1199 := by
    rcases h7178 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1200 := by
    rcases h7183 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7085 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24552 (p234 p1191 p1196 p1197 p1198 p1199 p1200 p1202 : Prop)
    (h24549 : p1197 ∨ p1191 ∨ p234)
    (h7164 : p1196 ∨ p1202)
    (h7174 : p1198 ∨ p1202)
    (h7179 : p1199 ∨ p1202)
    (h7184 : p1200 ∨ p1202)
    (h7085 : p234 ∨ p1191 ∨ (¬ p1196) ∨ (¬ p1197) ∨ (¬ p1198) ∨ (¬ p1199) ∨ (¬ p1200)) : p1202 ∨ p1191 ∨ p234 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1202) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1191) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p234) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1197 := by
    rcases h24549 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1196 := by
    rcases h7164 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1198 := by
    rcases h7174 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1199 := by
    rcases h7179 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1200 := by
    rcases h7184 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7085 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24553 (p234 p1191 p1196 p1197 p1198 p1199 p1200 p1203 : Prop)
    (h24549 : p1197 ∨ p1191 ∨ p234)
    (h7165 : p1196 ∨ p1203)
    (h7175 : p1198 ∨ p1203)
    (h7180 : p1199 ∨ p1203)
    (h7185 : p1200 ∨ p1203)
    (h7085 : p234 ∨ p1191 ∨ (¬ p1196) ∨ (¬ p1197) ∨ (¬ p1198) ∨ (¬ p1199) ∨ (¬ p1200)) : p1203 ∨ p1191 ∨ p234 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1203) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1191) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p234) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1197 := by
    rcases h24549 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1196 := by
    rcases h7165 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1198 := by
    rcases h7175 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1199 := by
    rcases h7180 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1200 := by
    rcases h7185 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7085 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24554 (p234 p1191 p1196 p1197 p1198 p1199 p1200 p1201 p1202 p1203 p1204 p1205 : Prop)
    (h24549 : p1197 ∨ p1191 ∨ p234)
    (h24550 : p1205 ∨ p1191 ∨ p234)
    (h24551 : p1201 ∨ p1191 ∨ p234)
    (h24552 : p1202 ∨ p1191 ∨ p234)
    (h24553 : p1203 ∨ p1191 ∨ p234)
    (h7110 : p234 ∨ p1191 ∨ (¬ p1201) ∨ (¬ p1202) ∨ (¬ p1203) ∨ (¬ p1204) ∨ (¬ p1205))
    (h7166 : p1196 ∨ p1204)
    (h7176 : p1198 ∨ p1204)
    (h7181 : p1199 ∨ p1204)
    (h7186 : p1200 ∨ p1204)
    (h7085 : p234 ∨ p1191 ∨ (¬ p1196) ∨ (¬ p1197) ∨ (¬ p1198) ∨ (¬ p1199) ∨ (¬ p1200)) : p1191 ∨ p234 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1191) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p234) := fun hu => hn (Or.inr hu)
  have u2 : p1197 := by
    rcases h24549 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1205 := by
    rcases h24550 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1201 := by
    rcases h24551 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1202 := by
    rcases h24552 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p1203 := by
    rcases h24553 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p1204) := by
    rcases h7110 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u6)
    · exact q5
    · exact False.elim (q6 u3)
  have u8 : p1196 := by
    rcases h7166 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p1198 := by
    rcases h7176 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p1199 := by
    rcases h7181 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p1200 := by
    rcases h7186 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h7085 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step24555 (p1116 p1117 p1128 p1130 p1131 p1132 p1133 p1134 : Prop)
    (h6723 : p1128 ∨ p1130)
    (h6724 : p1128 ∨ p1131)
    (h6725 : p1128 ∨ p1132)
    (h6726 : p1128 ∨ p1133)
    (h6727 : p1128 ∨ p1134)
    (h6635 : p1116 ∨ p1117 ∨ (¬ p1130) ∨ (¬ p1131) ∨ (¬ p1132) ∨ (¬ p1133) ∨ (¬ p1134)) : p1128 ∨ p1117 ∨ p1116 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1128) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1117) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1116) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1130 := by
    rcases h6723 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1131 := by
    rcases h6724 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1132 := by
    rcases h6725 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1133 := by
    rcases h6726 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1134 := by
    rcases h6727 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6635 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24556 (p1116 p1117 p1125 p1126 p1127 p1128 p1129 p1134 : Prop)
    (h24555 : p1128 ∨ p1117 ∨ p1116)
    (h6712 : p1125 ∨ p1134)
    (h6717 : p1126 ∨ p1134)
    (h6722 : p1127 ∨ p1134)
    (h6732 : p1129 ∨ p1134)
    (h6610 : p1116 ∨ p1117 ∨ (¬ p1125) ∨ (¬ p1126) ∨ (¬ p1127) ∨ (¬ p1128) ∨ (¬ p1129)) : p1134 ∨ p1117 ∨ p1116 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1134) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1117) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1116) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1128 := by
    rcases h24555 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1125 := by
    rcases h6712 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1126 := by
    rcases h6717 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1127 := by
    rcases h6722 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1129 := by
    rcases h6732 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6610 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24557 (p1116 p1117 p1125 p1126 p1127 p1128 p1129 p1130 : Prop)
    (h24555 : p1128 ∨ p1117 ∨ p1116)
    (h6708 : p1125 ∨ p1130)
    (h6713 : p1126 ∨ p1130)
    (h6718 : p1127 ∨ p1130)
    (h6728 : p1129 ∨ p1130)
    (h6610 : p1116 ∨ p1117 ∨ (¬ p1125) ∨ (¬ p1126) ∨ (¬ p1127) ∨ (¬ p1128) ∨ (¬ p1129)) : p1130 ∨ p1117 ∨ p1116 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1130) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1117) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1116) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1128 := by
    rcases h24555 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1125 := by
    rcases h6708 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1126 := by
    rcases h6713 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1127 := by
    rcases h6718 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1129 := by
    rcases h6728 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6610 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24558 (p1116 p1117 p1125 p1126 p1127 p1128 p1129 p1131 : Prop)
    (h24555 : p1128 ∨ p1117 ∨ p1116)
    (h6709 : p1125 ∨ p1131)
    (h6714 : p1126 ∨ p1131)
    (h6719 : p1127 ∨ p1131)
    (h6729 : p1129 ∨ p1131)
    (h6610 : p1116 ∨ p1117 ∨ (¬ p1125) ∨ (¬ p1126) ∨ (¬ p1127) ∨ (¬ p1128) ∨ (¬ p1129)) : p1131 ∨ p1117 ∨ p1116 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1131) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1117) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1116) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1128 := by
    rcases h24555 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1125 := by
    rcases h6709 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1126 := by
    rcases h6714 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1127 := by
    rcases h6719 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1129 := by
    rcases h6729 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6610 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24559 (p1116 p1117 p1125 p1126 p1127 p1128 p1129 p1132 : Prop)
    (h24555 : p1128 ∨ p1117 ∨ p1116)
    (h6710 : p1125 ∨ p1132)
    (h6715 : p1126 ∨ p1132)
    (h6720 : p1127 ∨ p1132)
    (h6730 : p1129 ∨ p1132)
    (h6610 : p1116 ∨ p1117 ∨ (¬ p1125) ∨ (¬ p1126) ∨ (¬ p1127) ∨ (¬ p1128) ∨ (¬ p1129)) : p1132 ∨ p1117 ∨ p1116 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1132) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1117) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1116) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1128 := by
    rcases h24555 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1125 := by
    rcases h6710 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1126 := by
    rcases h6715 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1127 := by
    rcases h6720 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1129 := by
    rcases h6730 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6610 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24560 (p1116 p1117 p1125 p1126 p1127 p1128 p1129 p1130 p1131 p1132 p1133 p1134 : Prop)
    (h24555 : p1128 ∨ p1117 ∨ p1116)
    (h24556 : p1134 ∨ p1117 ∨ p1116)
    (h24557 : p1130 ∨ p1117 ∨ p1116)
    (h24558 : p1131 ∨ p1117 ∨ p1116)
    (h24559 : p1132 ∨ p1117 ∨ p1116)
    (h6635 : p1116 ∨ p1117 ∨ (¬ p1130) ∨ (¬ p1131) ∨ (¬ p1132) ∨ (¬ p1133) ∨ (¬ p1134))
    (h6711 : p1125 ∨ p1133)
    (h6716 : p1126 ∨ p1133)
    (h6721 : p1127 ∨ p1133)
    (h6731 : p1129 ∨ p1133)
    (h6610 : p1116 ∨ p1117 ∨ (¬ p1125) ∨ (¬ p1126) ∨ (¬ p1127) ∨ (¬ p1128) ∨ (¬ p1129)) : p1117 ∨ p1116 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1117) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1116) := fun hu => hn (Or.inr hu)
  have u2 : p1128 := by
    rcases h24555 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1134 := by
    rcases h24556 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1130 := by
    rcases h24557 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1131 := by
    rcases h24558 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p1132 := by
    rcases h24559 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p1133) := by
    rcases h6635 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u6)
    · exact q5
    · exact False.elim (q6 u3)
  have u8 : p1125 := by
    rcases h6711 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p1126 := by
    rcases h6716 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p1127 := by
    rcases h6721 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p1129 := by
    rcases h6731 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h6610 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u11)

theorem step24561 (p456 p461 p465 p466 p467 p468 p469 p473 : Prop)
    (h2578 : p465 ∨ p473)
    (h2583 : p466 ∨ p473)
    (h2588 : p467 ∨ p473)
    (h2593 : p468 ∨ p473)
    (h2598 : p469 ∨ p473)
    (h2485 : p456 ∨ p461 ∨ (¬ p465) ∨ (¬ p466) ∨ (¬ p467) ∨ (¬ p468) ∨ (¬ p469)) : p473 ∨ p461 ∨ p456 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p473) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p461) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p456) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p465 := by
    rcases h2578 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p466 := by
    rcases h2583 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p467 := by
    rcases h2588 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p468 := by
    rcases h2593 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p469 := by
    rcases h2598 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2485 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24562 (p456 p461 p465 p470 p471 p472 p473 p474 : Prop)
    (h24561 : p473 ∨ p461 ∨ p456)
    (h2575 : p465 ∨ p470)
    (h2576 : p465 ∨ p471)
    (h2577 : p465 ∨ p472)
    (h2579 : p465 ∨ p474)
    (h2510 : p456 ∨ p461 ∨ (¬ p470) ∨ (¬ p471) ∨ (¬ p472) ∨ (¬ p473) ∨ (¬ p474)) : p465 ∨ p461 ∨ p456 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p465) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p461) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p456) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p473 := by
    rcases h24561 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p470 := by
    rcases h2575 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p471 := by
    rcases h2576 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p472 := by
    rcases h2577 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p474 := by
    rcases h2579 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2510 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24563 (p456 p461 p466 p470 p471 p472 p473 p474 : Prop)
    (h24561 : p473 ∨ p461 ∨ p456)
    (h2580 : p466 ∨ p470)
    (h2581 : p466 ∨ p471)
    (h2582 : p466 ∨ p472)
    (h2584 : p466 ∨ p474)
    (h2510 : p456 ∨ p461 ∨ (¬ p470) ∨ (¬ p471) ∨ (¬ p472) ∨ (¬ p473) ∨ (¬ p474)) : p466 ∨ p461 ∨ p456 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p466) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p461) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p456) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p473 := by
    rcases h24561 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p470 := by
    rcases h2580 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p471 := by
    rcases h2581 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p472 := by
    rcases h2582 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p474 := by
    rcases h2584 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2510 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24564 (p456 p461 p467 p470 p471 p472 p473 p474 : Prop)
    (h24561 : p473 ∨ p461 ∨ p456)
    (h2585 : p467 ∨ p470)
    (h2586 : p467 ∨ p471)
    (h2587 : p467 ∨ p472)
    (h2589 : p467 ∨ p474)
    (h2510 : p456 ∨ p461 ∨ (¬ p470) ∨ (¬ p471) ∨ (¬ p472) ∨ (¬ p473) ∨ (¬ p474)) : p467 ∨ p461 ∨ p456 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p467) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p461) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p456) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p473 := by
    rcases h24561 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p470 := by
    rcases h2585 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p471 := by
    rcases h2586 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p472 := by
    rcases h2587 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p474 := by
    rcases h2589 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2510 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24565 (p456 p461 p468 p470 p471 p472 p473 p474 : Prop)
    (h24561 : p473 ∨ p461 ∨ p456)
    (h2590 : p468 ∨ p470)
    (h2591 : p468 ∨ p471)
    (h2592 : p468 ∨ p472)
    (h2594 : p468 ∨ p474)
    (h2510 : p456 ∨ p461 ∨ (¬ p470) ∨ (¬ p471) ∨ (¬ p472) ∨ (¬ p473) ∨ (¬ p474)) : p468 ∨ p461 ∨ p456 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p468) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p461) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p456) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p473 := by
    rcases h24561 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p470 := by
    rcases h2590 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p471 := by
    rcases h2591 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p472 := by
    rcases h2592 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p474 := by
    rcases h2594 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2510 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24566 (p456 p461 p465 p466 p467 p468 p469 p470 p471 p472 p473 p474 : Prop)
    (h24561 : p473 ∨ p461 ∨ p456)
    (h24562 : p465 ∨ p461 ∨ p456)
    (h24563 : p466 ∨ p461 ∨ p456)
    (h24564 : p467 ∨ p461 ∨ p456)
    (h24565 : p468 ∨ p461 ∨ p456)
    (h2485 : p456 ∨ p461 ∨ (¬ p465) ∨ (¬ p466) ∨ (¬ p467) ∨ (¬ p468) ∨ (¬ p469))
    (h2595 : p469 ∨ p470)
    (h2596 : p469 ∨ p471)
    (h2597 : p469 ∨ p472)
    (h2599 : p469 ∨ p474)
    (h2510 : p456 ∨ p461 ∨ (¬ p470) ∨ (¬ p471) ∨ (¬ p472) ∨ (¬ p473) ∨ (¬ p474)) : p461 ∨ p456 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p461) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p456) := fun hu => hn (Or.inr hu)
  have u2 : p473 := by
    rcases h24561 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p465 := by
    rcases h24562 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p466 := by
    rcases h24563 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p467 := by
    rcases h24564 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p468 := by
    rcases h24565 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p469) := by
    rcases h2485 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p470 := by
    rcases h2595 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p471 := by
    rcases h2596 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p472 := by
    rcases h2597 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p474 := by
    rcases h2599 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h2510 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u11)

theorem step24567 (p8 p709 p716 p717 p718 p719 p720 p724 : Prop)
    (h4127 : p716 ∨ p724)
    (h4132 : p717 ∨ p724)
    (h4137 : p718 ∨ p724)
    (h4142 : p719 ∨ p724)
    (h4147 : p720 ∨ p724)
    (h4026 : p8 ∨ p709 ∨ (¬ p716) ∨ (¬ p717) ∨ (¬ p718) ∨ (¬ p719) ∨ (¬ p720)) : p724 ∨ p709 ∨ p8 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p724) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p709) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p716 := by
    rcases h4127 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p717 := by
    rcases h4132 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p718 := by
    rcases h4137 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p719 := by
    rcases h4142 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p720 := by
    rcases h4147 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4026 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24568 (p709 p713 p716 p721 p722 p723 p724 p725 : Prop)
    (h4124 : p716 ∨ p721)
    (h4125 : p716 ∨ p722)
    (h4126 : p716 ∨ p723)
    (h4128 : p716 ∨ p725)
    (h4049 : p709 ∨ p713 ∨ (¬ p721) ∨ (¬ p722) ∨ (¬ p723) ∨ (¬ p724) ∨ (¬ p725)) : p716 ∨ (¬ p724) ∨ p709 ∨ p713 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p716) := fun hu => hn (Or.inl hu)
  have u1 : p724 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p709) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p713) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p721 := by
    rcases h4124 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p722 := by
    rcases h4125 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p723 := by
    rcases h4126 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p725 := by
    rcases h4128 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4049 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step24569 (p709 p713 p717 p721 p722 p723 p724 p725 : Prop)
    (h4129 : p717 ∨ p721)
    (h4130 : p717 ∨ p722)
    (h4131 : p717 ∨ p723)
    (h4133 : p717 ∨ p725)
    (h4049 : p709 ∨ p713 ∨ (¬ p721) ∨ (¬ p722) ∨ (¬ p723) ∨ (¬ p724) ∨ (¬ p725)) : p717 ∨ (¬ p724) ∨ p709 ∨ p713 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p717) := fun hu => hn (Or.inl hu)
  have u1 : p724 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p709) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p713) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p721 := by
    rcases h4129 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p722 := by
    rcases h4130 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p723 := by
    rcases h4131 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p725 := by
    rcases h4133 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4049 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step24570 (p709 p713 p718 p721 p722 p723 p724 p725 : Prop)
    (h4134 : p718 ∨ p721)
    (h4135 : p718 ∨ p722)
    (h4136 : p718 ∨ p723)
    (h4138 : p718 ∨ p725)
    (h4049 : p709 ∨ p713 ∨ (¬ p721) ∨ (¬ p722) ∨ (¬ p723) ∨ (¬ p724) ∨ (¬ p725)) : p718 ∨ (¬ p724) ∨ p709 ∨ p713 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p718) := fun hu => hn (Or.inl hu)
  have u1 : p724 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p709) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p713) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p721 := by
    rcases h4134 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p722 := by
    rcases h4135 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p723 := by
    rcases h4136 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p725 := by
    rcases h4138 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4049 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step24571 (p709 p713 p719 p721 p722 p723 p724 p725 : Prop)
    (h4139 : p719 ∨ p721)
    (h4140 : p719 ∨ p722)
    (h4141 : p719 ∨ p723)
    (h4143 : p719 ∨ p725)
    (h4049 : p709 ∨ p713 ∨ (¬ p721) ∨ (¬ p722) ∨ (¬ p723) ∨ (¬ p724) ∨ (¬ p725)) : p719 ∨ (¬ p724) ∨ p709 ∨ p713 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p719) := fun hu => hn (Or.inl hu)
  have u1 : p724 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p709) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p713) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p721 := by
    rcases h4139 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p722 := by
    rcases h4140 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p723 := by
    rcases h4141 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p725 := by
    rcases h4143 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4049 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step24572 (p709 p713 p716 p717 p718 p719 p720 p721 p722 p723 p724 p725 : Prop)
    (h24568 : p716 ∨ (¬ p724) ∨ p709 ∨ p713)
    (h24569 : p717 ∨ (¬ p724) ∨ p709 ∨ p713)
    (h24570 : p718 ∨ (¬ p724) ∨ p709 ∨ p713)
    (h24571 : p719 ∨ (¬ p724) ∨ p709 ∨ p713)
    (h4024 : p709 ∨ p713 ∨ (¬ p716) ∨ (¬ p717) ∨ (¬ p718) ∨ (¬ p719) ∨ (¬ p720))
    (h4144 : p720 ∨ p721)
    (h4145 : p720 ∨ p722)
    (h4146 : p720 ∨ p723)
    (h4148 : p720 ∨ p725)
    (h4049 : p709 ∨ p713 ∨ (¬ p721) ∨ (¬ p722) ∨ (¬ p723) ∨ (¬ p724) ∨ (¬ p725)) : (¬ p724) ∨ p709 ∨ p713 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p724 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p709) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p713) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p716 := by
    rcases h24568 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u4 : p717 := by
    rcases h24569 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u5 : p718 := by
    rcases h24570 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u6 : p719 := by
    rcases h24571 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u7 : (¬ p720) := by
    rcases h4024 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p721 := by
    rcases h4144 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p722 := by
    rcases h4145 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p723 := by
    rcases h4146 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p725 := by
    rcases h4148 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h4049 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u11)

theorem step24573 (p8 p709 p713 p724 : Prop)
    (h24567 : p724 ∨ p709 ∨ p8)
    (h24572 : (¬ p724) ∨ p709 ∨ p713) : p709 ∨ p8 ∨ p713 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p709) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p8) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p713) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p724 := by
    rcases h24567 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h24572 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (u0 q1)
  · exact False.elim (u2 q2)

theorem step24574 (p3 p556 p568 p569 p570 p571 p572 p573 : Prop)
    (h23185 : (¬ p568) ∨ p3 ∨ p556)
    (h3232 : p568 ∨ p569)
    (h3233 : p568 ∨ p570)
    (h3234 : p568 ∨ p571)
    (h3235 : p568 ∨ p572)
    (h3236 : p568 ∨ p573)
    (h3139 : p3 ∨ p556 ∨ (¬ p569) ∨ (¬ p570) ∨ (¬ p571) ∨ (¬ p572) ∨ (¬ p573)) : p556 ∨ p3 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p556) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p568) := by
    rcases h23185 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u3 : p569 := by
    rcases h3232 with q0 | q1
    · exact False.elim (u2 q0)
    · exact q1
  have u4 : p570 := by
    rcases h3233 with q0 | q1
    · exact False.elim (u2 q0)
    · exact q1
  have u5 : p571 := by
    rcases h3234 with q0 | q1
    · exact False.elim (u2 q0)
    · exact q1
  have u6 : p572 := by
    rcases h3235 with q0 | q1
    · exact False.elim (u2 q0)
    · exact q1
  have u7 : p573 := by
    rcases h3236 with q0 | q1
    · exact False.elim (u2 q0)
    · exact q1
  rcases h3139 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24575 (p434 p440 p449 p450 p451 p452 p453 p454 : Prop)
    (h2467 : p449 ∨ p450)
    (h2468 : p449 ∨ p451)
    (h2469 : p449 ∨ p452)
    (h2471 : p449 ∨ p454)
    (h2394 : p434 ∨ p440 ∨ (¬ p450) ∨ (¬ p451) ∨ (¬ p452) ∨ (¬ p453) ∨ (¬ p454)) : p449 ∨ (¬ p453) ∨ p440 ∨ p434 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p449) := fun hu => hn (Or.inl hu)
  have u1 : p453 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p440) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p434) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p450 := by
    rcases h2467 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p451 := by
    rcases h2468 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p452 := by
    rcases h2469 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p454 := by
    rcases h2471 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2394 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step24576 (p434 p440 p445 p446 p447 p448 p449 p454 : Prop)
    (h2451 : p445 ∨ p454)
    (h2456 : p446 ∨ p454)
    (h2461 : p447 ∨ p454)
    (h2466 : p448 ∨ p454)
    (h2369 : p434 ∨ p440 ∨ (¬ p445) ∨ (¬ p446) ∨ (¬ p447) ∨ (¬ p448) ∨ (¬ p449)) : p454 ∨ (¬ p449) ∨ p440 ∨ p434 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p454) := fun hu => hn (Or.inl hu)
  have u1 : p449 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p440) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p434) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p445 := by
    rcases h2451 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p446 := by
    rcases h2456 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p447 := by
    rcases h2461 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p448 := by
    rcases h2466 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2369 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24578 (p434 p499 p595 p598 p600 p614 p616 p690 p1542 p1545 : Prop)
    (h21715 : p614 ∨ p595)
    (h21790 : p616 ∨ p595)
    (h10590 : (¬ p499) ∨ p595 ∨ (¬ p600))
    (h19210 : (¬ p434) ∨ (¬ p499) ∨ (¬ p616) ∨ (¬ p1545))
    (h20833 : p598 ∨ p600)
    (h20851 : p1542 ∨ p1545)
    (h16740 : (¬ p499) ∨ (¬ p598) ∨ (¬ p614) ∨ (¬ p690) ∨ (¬ p1542)) : p595 ∨ (¬ p434) ∨ (¬ p499) ∨ (¬ p690) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p595) := fun hu => hn (Or.inl hu)
  have u1 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p614 := by
    rcases h21715 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p616 := by
    rcases h21790 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : (¬ p600) := by
    rcases h10590 with q0 | q1 | q2
    · exact False.elim (q0 u2)
    · exact False.elim (u0 q1)
    · exact q2
  have u7 : (¬ p1545) := by
    rcases h19210 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u1)
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u5)
    · exact q3
  have u8 : p598 := by
    rcases h20833 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1542 := by
    rcases h20851 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h16740 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u9)

theorem step24579 (p5 p69 p595 p1188 : Prop)
    (h16623 : p5 ∨ (¬ p69))
    (h23632 : p5 ∨ (¬ p1188) ∨ p69 ∨ (¬ p595)) : p5 ∨ (¬ p1188) ∨ (¬ p595) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p5) := fun hu => hn (Or.inl hu)
  have u1 : p1188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p69) := by
    rcases h16623 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h23632 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (u3 q2)
  · exact False.elim (q3 u2)

theorem step24583 (p41 p163 p166 p170 p225 p344 p918 p928 : Prop)
    (h22025 : p918 ∨ p928)
    (h13917 : (¬ p41) ∨ (¬ p170) ∨ p928)
    (h18423 : (¬ p41) ∨ (¬ p166) ∨ (¬ p225) ∨ (¬ p344) ∨ (¬ p918))
    (h23527 : p166 ∨ p170 ∨ p163) : p928 ∨ (¬ p344) ∨ (¬ p41) ∨ p163 ∨ (¬ p225) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p928) := fun hu => hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p918 := by
    rcases h22025 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : (¬ p170) := by
    rcases h13917 with q0 | q1 | q2
    · exact False.elim (q0 u2)
    · exact q1
    · exact False.elim (u0 q2)
  have u7 : (¬ p166) := by
    rcases h18423 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u2)
    · exact q1
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u1)
    · exact False.elim (q4 u5)
  rcases h23527 with q0 | q1 | q2
  · exact False.elim (u7 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (u3 q2)

theorem step24585 (p1385 p1392 p1396 p1397 p1398 p1399 p1400 p1405 : Prop)
    (h24507 : (¬ p1405) ∨ p1392 ∨ p1385)
    (h8453 : p1396 ∨ p1405)
    (h8458 : p1397 ∨ p1405)
    (h8463 : p1398 ∨ p1405)
    (h8468 : p1399 ∨ p1405)
    (h8473 : p1400 ∨ p1405)
    (h8360 : p1385 ∨ p1392 ∨ (¬ p1396) ∨ (¬ p1397) ∨ (¬ p1398) ∨ (¬ p1399) ∨ (¬ p1400)) : p1392 ∨ p1385 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1392) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1385) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p1405) := by
    rcases h24507 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1396 := by
    rcases h8453 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : p1397 := by
    rcases h8458 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p1398 := by
    rcases h8463 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p1399 := by
    rcases h8468 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p1400 := by
    rcases h8473 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h8360 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24586 (p12 p224 p225 p431 p657 p662 p666 p734 p1036 p1332 : Prop)
    (h22941 : p1036 ∨ p12)
    (h14227 : (¬ p225) ∨ (¬ p662) ∨ p1036)
    (h21721 : p662 ∨ p657)
    (h6747 : (¬ p224) ∨ (¬ p657))
    (h22413 : p666 ∨ p224)
    (h10844 : p224 ∨ (¬ p734) ∨ (¬ p1332))
    (h19074 : (¬ p12) ∨ (¬ p225) ∨ (¬ p431) ∨ (¬ p666) ∨ (¬ p734))
    (h22367 : p431 ∨ p1332) : p1036 ∨ (¬ p225) ∨ (¬ p734) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1036) := fun hu => hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p12 := by
    rcases h22941 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : (¬ p662) := by
    rcases h14227 with q0 | q1 | q2
    · exact False.elim (q0 u1)
    · exact q1
    · exact False.elim (u0 q2)
  have u5 : p657 := by
    rcases h21721 with q0 | q1
    · exact False.elim (u4 q0)
    · exact q1
  have u6 : (¬ p224) := by
    rcases h6747 with q0 | q1
    · exact q0
    · exact False.elim (q1 u5)
  have u7 : p666 := by
    rcases h22413 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : (¬ p1332) := by
    rcases h10844 with q0 | q1 | q2
    · exact False.elim (u6 q0)
    · exact False.elim (q1 u2)
    · exact q2
  have u9 : (¬ p431) := by
    rcases h19074 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u3)
    · exact False.elim (q1 u1)
    · exact q2
    · exact False.elim (q3 u7)
    · exact False.elim (q4 u2)
  rcases h22367 with q0 | q1
  · exact False.elim (u9 q0)
  · exact False.elim (u8 q1)

theorem step24587 (p434 p436 p445 p446 p447 p448 p449 p454 : Prop)
    (h2451 : p445 ∨ p454)
    (h2456 : p446 ∨ p454)
    (h2461 : p447 ∨ p454)
    (h2466 : p448 ∨ p454)
    (h2471 : p449 ∨ p454)
    (h2349 : p434 ∨ p436 ∨ (¬ p445) ∨ (¬ p446) ∨ (¬ p447) ∨ (¬ p448) ∨ (¬ p449)) : p454 ∨ p436 ∨ p434 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p454) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p436) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p434) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p445 := by
    rcases h2451 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p446 := by
    rcases h2456 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p447 := by
    rcases h2461 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p448 := by
    rcases h2466 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p449 := by
    rcases h2471 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2349 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24588 (p434 p436 p445 p446 p447 p448 p449 p450 : Prop)
    (h2447 : p445 ∨ p450)
    (h2452 : p446 ∨ p450)
    (h2457 : p447 ∨ p450)
    (h2462 : p448 ∨ p450)
    (h2467 : p449 ∨ p450)
    (h2349 : p434 ∨ p436 ∨ (¬ p445) ∨ (¬ p446) ∨ (¬ p447) ∨ (¬ p448) ∨ (¬ p449)) : p450 ∨ p436 ∨ p434 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p450) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p436) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p434) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p445 := by
    rcases h2447 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p446 := by
    rcases h2452 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p447 := by
    rcases h2457 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p448 := by
    rcases h2462 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p449 := by
    rcases h2467 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2349 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24589 (p434 p436 p445 p446 p447 p448 p449 p451 : Prop)
    (h2448 : p445 ∨ p451)
    (h2453 : p446 ∨ p451)
    (h2458 : p447 ∨ p451)
    (h2463 : p448 ∨ p451)
    (h2468 : p449 ∨ p451)
    (h2349 : p434 ∨ p436 ∨ (¬ p445) ∨ (¬ p446) ∨ (¬ p447) ∨ (¬ p448) ∨ (¬ p449)) : p451 ∨ p436 ∨ p434 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p451) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p436) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p434) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p445 := by
    rcases h2448 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p446 := by
    rcases h2453 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p447 := by
    rcases h2458 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p448 := by
    rcases h2463 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p449 := by
    rcases h2468 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2349 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24590 (p434 p436 p445 p446 p447 p448 p449 p452 : Prop)
    (h2449 : p445 ∨ p452)
    (h2454 : p446 ∨ p452)
    (h2459 : p447 ∨ p452)
    (h2464 : p448 ∨ p452)
    (h2469 : p449 ∨ p452)
    (h2349 : p434 ∨ p436 ∨ (¬ p445) ∨ (¬ p446) ∨ (¬ p447) ∨ (¬ p448) ∨ (¬ p449)) : p452 ∨ p436 ∨ p434 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p452) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p436) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p434) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p445 := by
    rcases h2449 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p446 := by
    rcases h2454 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p447 := by
    rcases h2459 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p448 := by
    rcases h2464 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p449 := by
    rcases h2469 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2349 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24591 (p434 p436 p445 p446 p447 p448 p449 p450 p451 p452 p453 p454 : Prop)
    (h2374 : p434 ∨ p436 ∨ (¬ p450) ∨ (¬ p451) ∨ (¬ p452) ∨ (¬ p453) ∨ (¬ p454))
    (h2450 : p445 ∨ p453)
    (h2455 : p446 ∨ p453)
    (h2460 : p447 ∨ p453)
    (h2465 : p448 ∨ p453)
    (h2470 : p449 ∨ p453)
    (h2349 : p434 ∨ p436 ∨ (¬ p445) ∨ (¬ p446) ∨ (¬ p447) ∨ (¬ p448) ∨ (¬ p449)) : (¬ p452) ∨ (¬ p451) ∨ (¬ p454) ∨ p434 ∨ p436 ∨ (¬ p450) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p451 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p454 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p434) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p436) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p450 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p453) := by
    rcases h2374 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u4 q1)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u1)
    · exact False.elim (q4 u0)
    · exact q5
    · exact False.elim (q6 u2)
  have u7 : p445 := by
    rcases h2450 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p446 := by
    rcases h2455 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p447 := by
    rcases h2460 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p448 := by
    rcases h2465 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p449 := by
    rcases h2470 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h2349 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step24592 (p434 p436 p450 p451 p452 p454 : Prop)
    (h24587 : p454 ∨ p436 ∨ p434)
    (h24588 : p450 ∨ p436 ∨ p434)
    (h24589 : p451 ∨ p436 ∨ p434)
    (h24590 : p452 ∨ p436 ∨ p434)
    (h24591 : (¬ p452) ∨ (¬ p451) ∨ (¬ p454) ∨ p434 ∨ p436 ∨ (¬ p450)) : p436 ∨ p434 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p436) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p434) := fun hu => hn (Or.inr hu)
  have u2 : p454 := by
    rcases h24587 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p450 := by
    rcases h24588 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p451 := by
    rcases h24589 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p452 := by
    rcases h24590 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h24591 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (u1 q3)
  · exact False.elim (u0 q4)
  · exact False.elim (q5 u3)

theorem step24593 (p126 p303 p386 p387 p517 p518 p858 p1325 p1452 : Prop)
    (h21708 : p303 ∨ p386)
    (h21394 : p387 ∨ p303)
    (h10679 : (¬ p387) ∨ (¬ p518) ∨ (¬ p858))
    (h16507 : (¬ p386) ∨ (¬ p517) ∨ (¬ p858) ∨ (¬ p1325) ∨ (¬ p1452))
    (h20901 : p517 ∨ p518 ∨ p126) : (¬ p858) ∨ (¬ p1325) ∨ (¬ p1452) ∨ p303 ∨ p126 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p126) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p386 := by
    rcases h21708 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  have u6 : p387 := by
    rcases h21394 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : (¬ p518) := by
    rcases h10679 with q0 | q1 | q2
    · exact False.elim (q0 u6)
    · exact q1
    · exact False.elim (q2 u0)
  have u8 : (¬ p517) := by
    rcases h16507 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u5)
    · exact q1
    · exact False.elim (q2 u0)
    · exact False.elim (q3 u1)
    · exact False.elim (q4 u2)
  rcases h20901 with q0 | q1 | q2
  · exact False.elim (u8 q0)
  · exact False.elim (u7 q1)
  · exact False.elim (u4 q2)

theorem step24595 (p10 p328 p333 p337 p338 p339 p340 p341 : Prop)
    (h1804 : p333 ∨ p337)
    (h1805 : p333 ∨ p338)
    (h1806 : p333 ∨ p339)
    (h1808 : p333 ∨ p341)
    (h1734 : p10 ∨ p328 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341)) : p333 ∨ (¬ p340) ∨ p328 ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p333) := fun hu => hn (Or.inl hu)
  have u1 : p340 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p328) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p337 := by
    rcases h1804 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p338 := by
    rcases h1805 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p339 := by
    rcases h1806 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p341 := by
    rcases h1808 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1734 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step24596 (p10 p328 p332 p337 p338 p339 p340 p341 : Prop)
    (h1799 : p332 ∨ p337)
    (h1800 : p332 ∨ p338)
    (h1801 : p332 ∨ p339)
    (h1803 : p332 ∨ p341)
    (h1734 : p10 ∨ p328 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341)) : p332 ∨ (¬ p340) ∨ p328 ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p332) := fun hu => hn (Or.inl hu)
  have u1 : p340 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p328) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p337 := by
    rcases h1799 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p338 := by
    rcases h1800 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p339 := by
    rcases h1801 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p341 := by
    rcases h1803 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1734 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step24597 (p10 p328 p334 p337 p338 p339 p340 p341 : Prop)
    (h1809 : p334 ∨ p337)
    (h1810 : p334 ∨ p338)
    (h1811 : p334 ∨ p339)
    (h1813 : p334 ∨ p341)
    (h1734 : p10 ∨ p328 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341)) : p334 ∨ (¬ p340) ∨ p328 ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p334) := fun hu => hn (Or.inl hu)
  have u1 : p340 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p328) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p337 := by
    rcases h1809 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p338 := by
    rcases h1810 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p339 := by
    rcases h1811 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p341 := by
    rcases h1813 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1734 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step24598 (p10 p328 p335 p337 p338 p339 p340 p341 : Prop)
    (h1814 : p335 ∨ p337)
    (h1815 : p335 ∨ p338)
    (h1816 : p335 ∨ p339)
    (h1818 : p335 ∨ p341)
    (h1734 : p10 ∨ p328 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341)) : p335 ∨ (¬ p340) ∨ p328 ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p335) := fun hu => hn (Or.inl hu)
  have u1 : p340 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p328) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p337 := by
    rcases h1814 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p338 := by
    rcases h1815 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p339 := by
    rcases h1816 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p341 := by
    rcases h1818 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1734 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step24599 (p10 p328 p332 p333 p334 p335 p336 p337 p338 p339 p340 p341 : Prop)
    (h24595 : p333 ∨ (¬ p340) ∨ p328 ∨ p10)
    (h24596 : p332 ∨ (¬ p340) ∨ p328 ∨ p10)
    (h24597 : p334 ∨ (¬ p340) ∨ p328 ∨ p10)
    (h24598 : p335 ∨ (¬ p340) ∨ p328 ∨ p10)
    (h1709 : p10 ∨ p328 ∨ (¬ p332) ∨ (¬ p333) ∨ (¬ p334) ∨ (¬ p335) ∨ (¬ p336))
    (h1819 : p336 ∨ p337)
    (h1820 : p336 ∨ p338)
    (h1821 : p336 ∨ p339)
    (h1823 : p336 ∨ p341)
    (h1734 : p10 ∨ p328 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341)) : (¬ p340) ∨ p328 ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p340 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p328) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p333 := by
    rcases h24595 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u4 : p332 := by
    rcases h24596 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u5 : p334 := by
    rcases h24597 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u6 : p335 := by
    rcases h24598 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u7 : (¬ p336) := by
    rcases h1709 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u3)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p337 := by
    rcases h1819 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p338 := by
    rcases h1820 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p339 := by
    rcases h1821 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p341 := by
    rcases h1823 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h1734 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u11)

theorem step24600 (p10 p328 p332 p333 p334 p335 p336 p340 : Prop)
    (h24599 : (¬ p340) ∨ p328 ∨ p10)
    (h1802 : p332 ∨ p340)
    (h1807 : p333 ∨ p340)
    (h1812 : p334 ∨ p340)
    (h1817 : p335 ∨ p340)
    (h1822 : p336 ∨ p340)
    (h1709 : p10 ∨ p328 ∨ (¬ p332) ∨ (¬ p333) ∨ (¬ p334) ∨ (¬ p335) ∨ (¬ p336)) : p328 ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p328) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p10) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p340) := by
    rcases h24599 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p332 := by
    rcases h1802 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : p333 := by
    rcases h1807 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p334 := by
    rcases h1812 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p335 := by
    rcases h1817 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p336 := by
    rcases h1822 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h1709 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24601 (p1232 p1237 p1239 p1240 p1241 p1242 p1243 p1247 : Prop)
    (h7431 : p1239 ∨ p1247)
    (h7436 : p1240 ∨ p1247)
    (h7441 : p1241 ∨ p1247)
    (h7446 : p1242 ∨ p1247)
    (h7451 : p1243 ∨ p1247)
    (h7341 : p1232 ∨ p1237 ∨ (¬ p1239) ∨ (¬ p1240) ∨ (¬ p1241) ∨ (¬ p1242) ∨ (¬ p1243)) : p1247 ∨ p1237 ∨ p1232 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1247) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1237) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1232) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1239 := by
    rcases h7431 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1240 := by
    rcases h7436 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1241 := by
    rcases h7441 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1242 := by
    rcases h7446 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1243 := by
    rcases h7451 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7341 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24602 (p1232 p1237 p1239 p1244 p1245 p1246 p1247 p1248 : Prop)
    (h24601 : p1247 ∨ p1237 ∨ p1232)
    (h7428 : p1239 ∨ p1244)
    (h7429 : p1239 ∨ p1245)
    (h7430 : p1239 ∨ p1246)
    (h7432 : p1239 ∨ p1248)
    (h7366 : p1232 ∨ p1237 ∨ (¬ p1244) ∨ (¬ p1245) ∨ (¬ p1246) ∨ (¬ p1247) ∨ (¬ p1248)) : p1239 ∨ p1237 ∨ p1232 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1239) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1237) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1232) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1247 := by
    rcases h24601 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1244 := by
    rcases h7428 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1245 := by
    rcases h7429 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1246 := by
    rcases h7430 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1248 := by
    rcases h7432 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7366 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24603 (p1232 p1237 p1240 p1244 p1245 p1246 p1247 p1248 : Prop)
    (h24601 : p1247 ∨ p1237 ∨ p1232)
    (h7433 : p1240 ∨ p1244)
    (h7434 : p1240 ∨ p1245)
    (h7435 : p1240 ∨ p1246)
    (h7437 : p1240 ∨ p1248)
    (h7366 : p1232 ∨ p1237 ∨ (¬ p1244) ∨ (¬ p1245) ∨ (¬ p1246) ∨ (¬ p1247) ∨ (¬ p1248)) : p1240 ∨ p1237 ∨ p1232 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1240) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1237) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1232) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1247 := by
    rcases h24601 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1244 := by
    rcases h7433 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1245 := by
    rcases h7434 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1246 := by
    rcases h7435 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1248 := by
    rcases h7437 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7366 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24604 (p1232 p1237 p1241 p1244 p1245 p1246 p1247 p1248 : Prop)
    (h24601 : p1247 ∨ p1237 ∨ p1232)
    (h7438 : p1241 ∨ p1244)
    (h7439 : p1241 ∨ p1245)
    (h7440 : p1241 ∨ p1246)
    (h7442 : p1241 ∨ p1248)
    (h7366 : p1232 ∨ p1237 ∨ (¬ p1244) ∨ (¬ p1245) ∨ (¬ p1246) ∨ (¬ p1247) ∨ (¬ p1248)) : p1241 ∨ p1237 ∨ p1232 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1241) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1237) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1232) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1247 := by
    rcases h24601 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1244 := by
    rcases h7438 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1245 := by
    rcases h7439 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1246 := by
    rcases h7440 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1248 := by
    rcases h7442 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7366 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24605 (p1232 p1237 p1242 p1244 p1245 p1246 p1247 p1248 : Prop)
    (h24601 : p1247 ∨ p1237 ∨ p1232)
    (h7443 : p1242 ∨ p1244)
    (h7444 : p1242 ∨ p1245)
    (h7445 : p1242 ∨ p1246)
    (h7447 : p1242 ∨ p1248)
    (h7366 : p1232 ∨ p1237 ∨ (¬ p1244) ∨ (¬ p1245) ∨ (¬ p1246) ∨ (¬ p1247) ∨ (¬ p1248)) : p1242 ∨ p1237 ∨ p1232 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1242) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1237) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1232) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1247 := by
    rcases h24601 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1244 := by
    rcases h7443 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1245 := by
    rcases h7444 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1246 := by
    rcases h7445 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1248 := by
    rcases h7447 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7366 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24606 (p1232 p1237 p1239 p1240 p1241 p1242 p1243 p1244 p1245 p1246 p1247 p1248 : Prop)
    (h24601 : p1247 ∨ p1237 ∨ p1232)
    (h24602 : p1239 ∨ p1237 ∨ p1232)
    (h24603 : p1240 ∨ p1237 ∨ p1232)
    (h24604 : p1241 ∨ p1237 ∨ p1232)
    (h24605 : p1242 ∨ p1237 ∨ p1232)
    (h7341 : p1232 ∨ p1237 ∨ (¬ p1239) ∨ (¬ p1240) ∨ (¬ p1241) ∨ (¬ p1242) ∨ (¬ p1243))
    (h7448 : p1243 ∨ p1244)
    (h7449 : p1243 ∨ p1245)
    (h7450 : p1243 ∨ p1246)
    (h7452 : p1243 ∨ p1248)
    (h7366 : p1232 ∨ p1237 ∨ (¬ p1244) ∨ (¬ p1245) ∨ (¬ p1246) ∨ (¬ p1247) ∨ (¬ p1248)) : p1237 ∨ p1232 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1237) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1232) := fun hu => hn (Or.inr hu)
  have u2 : p1247 := by
    rcases h24601 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1239 := by
    rcases h24602 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1240 := by
    rcases h24603 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1241 := by
    rcases h24604 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p1242 := by
    rcases h24605 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p1243) := by
    rcases h7341 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p1244 := by
    rcases h7448 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p1245 := by
    rcases h7449 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p1246 := by
    rcases h7450 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p1248 := by
    rcases h7452 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h7366 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u11)

theorem step24613 (p224 p669 p674 p675 p676 p677 p678 p679 : Prop)
    (h3879 : p674 ∨ p675)
    (h3880 : p674 ∨ p676)
    (h3881 : p674 ∨ p677)
    (h3882 : p674 ∨ p678)
    (h3798 : p224 ∨ p669 ∨ (¬ p675) ∨ (¬ p676) ∨ (¬ p677) ∨ (¬ p678) ∨ (¬ p679)) : p674 ∨ (¬ p679) ∨ p669 ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p674) := fun hu => hn (Or.inl hu)
  have u1 : p679 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p669) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p675 := by
    rcases h3879 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p676 := by
    rcases h3880 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p677 := by
    rcases h3881 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p678 := by
    rcases h3882 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3798 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24614 (p224 p669 p670 p671 p672 p673 p674 p675 : Prop)
    (h3859 : p670 ∨ p675)
    (h3864 : p671 ∨ p675)
    (h3869 : p672 ∨ p675)
    (h3874 : p673 ∨ p675)
    (h3773 : p224 ∨ p669 ∨ (¬ p670) ∨ (¬ p671) ∨ (¬ p672) ∨ (¬ p673) ∨ (¬ p674)) : p675 ∨ (¬ p674) ∨ p669 ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p675) := fun hu => hn (Or.inl hu)
  have u1 : p674 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p669) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p670 := by
    rcases h3859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p671 := by
    rcases h3864 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p672 := by
    rcases h3869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p673 := by
    rcases h3874 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3773 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24615 (p224 p669 p670 p671 p672 p673 p674 p676 : Prop)
    (h3860 : p670 ∨ p676)
    (h3865 : p671 ∨ p676)
    (h3870 : p672 ∨ p676)
    (h3875 : p673 ∨ p676)
    (h3773 : p224 ∨ p669 ∨ (¬ p670) ∨ (¬ p671) ∨ (¬ p672) ∨ (¬ p673) ∨ (¬ p674)) : p676 ∨ (¬ p674) ∨ p669 ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p676) := fun hu => hn (Or.inl hu)
  have u1 : p674 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p669) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p670 := by
    rcases h3860 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p671 := by
    rcases h3865 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p672 := by
    rcases h3870 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p673 := by
    rcases h3875 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3773 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24616 (p224 p669 p670 p671 p672 p673 p674 p677 : Prop)
    (h3861 : p670 ∨ p677)
    (h3866 : p671 ∨ p677)
    (h3871 : p672 ∨ p677)
    (h3876 : p673 ∨ p677)
    (h3773 : p224 ∨ p669 ∨ (¬ p670) ∨ (¬ p671) ∨ (¬ p672) ∨ (¬ p673) ∨ (¬ p674)) : p677 ∨ (¬ p674) ∨ p669 ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p677) := fun hu => hn (Or.inl hu)
  have u1 : p674 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p669) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p670 := by
    rcases h3861 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p671 := by
    rcases h3866 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p672 := by
    rcases h3871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p673 := by
    rcases h3876 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3773 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24617 (p224 p669 p670 p671 p672 p673 p674 p675 p676 p677 p678 p679 : Prop)
    (h24613 : p674 ∨ (¬ p679) ∨ p669 ∨ p224)
    (h24614 : p675 ∨ (¬ p674) ∨ p669 ∨ p224)
    (h24615 : p676 ∨ (¬ p674) ∨ p669 ∨ p224)
    (h24616 : p677 ∨ (¬ p674) ∨ p669 ∨ p224)
    (h3798 : p224 ∨ p669 ∨ (¬ p675) ∨ (¬ p676) ∨ (¬ p677) ∨ (¬ p678) ∨ (¬ p679))
    (h3862 : p670 ∨ p678)
    (h3867 : p671 ∨ p678)
    (h3872 : p672 ∨ p678)
    (h3877 : p673 ∨ p678)
    (h3773 : p224 ∨ p669 ∨ (¬ p670) ∨ (¬ p671) ∨ (¬ p672) ∨ (¬ p673) ∨ (¬ p674)) : (¬ p679) ∨ p669 ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p679 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p669) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p674 := by
    rcases h24613 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u4 : p675 := by
    rcases h24614 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u5 : p676 := by
    rcases h24615 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u6 : p677 := by
    rcases h24616 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u7 : (¬ p678) := by
    rcases h3798 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u6)
    · exact q5
    · exact False.elim (q6 u0)
  have u8 : p670 := by
    rcases h3862 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p671 := by
    rcases h3867 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p672 := by
    rcases h3872 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p673 := by
    rcases h3877 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h3773 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u3)

theorem step24618 (p224 p669 p670 p671 p672 p673 p674 p679 : Prop)
    (h24617 : (¬ p679) ∨ p669 ∨ p224)
    (h3863 : p670 ∨ p679)
    (h3868 : p671 ∨ p679)
    (h3873 : p672 ∨ p679)
    (h3878 : p673 ∨ p679)
    (h3883 : p674 ∨ p679)
    (h3773 : p224 ∨ p669 ∨ (¬ p670) ∨ (¬ p671) ∨ (¬ p672) ∨ (¬ p673) ∨ (¬ p674)) : p669 ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p669) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p679) := by
    rcases h24617 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p670 := by
    rcases h3863 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : p671 := by
    rcases h3868 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p672 := by
    rcases h3873 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p673 := by
    rcases h3878 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p674 := by
    rcases h3883 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h3773 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24621 (p101 p121 p532 p1035 p1084 p1206 p1212 p1325 p1452 : Prop)
    (h8762 : (¬ p121) ∨ (¬ p1206))
    (h21957 : p1212 ∨ p1206)
    (h19994 : (¬ p101) ∨ (¬ p121) ∨ (¬ p1325) ∨ (¬ p1452))
    (h18364 : (¬ p101) ∨ (¬ p532) ∨ (¬ p1035) ∨ (¬ p1084) ∨ (¬ p1212))
    (h21329 : p1452 ∨ p532) : (¬ p101) ∨ (¬ p1035) ∨ (¬ p121) ∨ (¬ p1084) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1035 := by
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
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p1206) := by
    rcases h8762 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u6 : p1212 := by
    rcases h21957 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u7 : (¬ p1452) := by
    rcases h19994 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u0)
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u4)
    · exact q3
  have u8 : (¬ p532) := by
    rcases h18364 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u3)
    · exact False.elim (q4 u6)
  rcases h21329 with q0 | q1
  · exact False.elim (u7 q0)
  · exact False.elim (u8 q1)

theorem step24625 (p41 p63 p121 p142 p499 : Prop)
    (h18566 : (¬ p41) ∨ (¬ p63) ∨ (¬ p121) ∨ (¬ p142))
    (h23966 : p499 ∨ p142 ∨ (¬ p41) ∨ (¬ p63)) : (¬ p41) ∨ p499 ∨ (¬ p63) ∨ (¬ p121) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p499) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p142) := by
    rcases h18566 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u0)
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u3)
    · exact q3
  rcases h23966 with q0 | q1 | q2 | q3
  · exact False.elim (u1 q0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u2)

theorem step24626 (p346 p349 p352 p353 p354 p355 p356 p357 p358 p359 p360 p361 : Prop)
    (h1836 : p346 ∨ p349 ∨ (¬ p352) ∨ (¬ p353) ∨ (¬ p354) ∨ (¬ p355) ∨ (¬ p356))
    (h1925 : p352 ∨ p357)
    (h1926 : p352 ∨ p358)
    (h1927 : p352 ∨ p359)
    (h1928 : p352 ∨ p360)
    (h1929 : p352 ∨ p361)
    (h1861 : p346 ∨ p349 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361)) : p349 ∨ (¬ p354) ∨ (¬ p353) ∨ p346 ∨ (¬ p355) ∨ (¬ p356) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p349) := fun hu => hn (Or.inl hu)
  have u1 : p354 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p353 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p346) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p355 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p356 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p352) := by
    rcases h1836 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u0 q1)
    · exact q2
    · exact False.elim (q3 u2)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u5)
  have u7 : p357 := by
    rcases h1925 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p358 := by
    rcases h1926 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p359 := by
    rcases h1927 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p360 := by
    rcases h1928 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p361 := by
    rcases h1929 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h1861 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step24627 (p346 p349 p353 p354 p355 p356 : Prop)
    (h22453 : p356 ∨ p349 ∨ p346)
    (h22454 : p355 ∨ p349 ∨ p346)
    (h22455 : p354 ∨ p349 ∨ p346)
    (h22456 : p353 ∨ p349 ∨ p346)
    (h24626 : p349 ∨ (¬ p354) ∨ (¬ p353) ∨ p346 ∨ (¬ p355) ∨ (¬ p356)) : p349 ∨ p346 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p349) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p346) := fun hu => hn (Or.inr hu)
  have u2 : p356 := by
    rcases h22453 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p355 := by
    rcases h22454 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p354 := by
    rcases h22455 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p353 := by
    rcases h22456 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h24626 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u2)

theorem step24628 (p796 p802 p808 p809 p810 p811 p812 p813 : Prop)
    (h4663 : p808 ∨ p809)
    (h4664 : p808 ∨ p810)
    (h4666 : p808 ∨ p812)
    (h4667 : p808 ∨ p813)
    (h4581 : p796 ∨ p802 ∨ (¬ p809) ∨ (¬ p810) ∨ (¬ p811) ∨ (¬ p812) ∨ (¬ p813)) : p808 ∨ (¬ p811) ∨ p802 ∨ p796 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p808) := fun hu => hn (Or.inl hu)
  have u1 : p811 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p802) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p796) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p809 := by
    rcases h4663 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p810 := by
    rcases h4664 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p812 := by
    rcases h4666 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p813 := by
    rcases h4667 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4581 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24629 (p796 p802 p804 p805 p806 p807 p808 p812 : Prop)
    (h4646 : p804 ∨ p812)
    (h4651 : p805 ∨ p812)
    (h4656 : p806 ∨ p812)
    (h4661 : p807 ∨ p812)
    (h4556 : p796 ∨ p802 ∨ (¬ p804) ∨ (¬ p805) ∨ (¬ p806) ∨ (¬ p807) ∨ (¬ p808)) : p812 ∨ (¬ p808) ∨ p802 ∨ p796 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p812) := fun hu => hn (Or.inl hu)
  have u1 : p808 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p802) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p796) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p804 := by
    rcases h4646 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p805 := by
    rcases h4651 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p806 := by
    rcases h4656 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p807 := by
    rcases h4661 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4556 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24630 (p796 p802 p804 p805 p806 p807 p808 p813 : Prop)
    (h21018 : (¬ p796) ∨ p802)
    (h4647 : p804 ∨ p813)
    (h4652 : p805 ∨ p813)
    (h4657 : p806 ∨ p813)
    (h4662 : p807 ∨ p813)
    (h4556 : p796 ∨ p802 ∨ (¬ p804) ∨ (¬ p805) ∨ (¬ p806) ∨ (¬ p807) ∨ (¬ p808)) : p813 ∨ (¬ p808) ∨ p802 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p813) := fun hu => hn (Or.inl hu)
  have u1 : p808 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p802) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : (¬ p796) := by
    rcases h21018 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : p804 := by
    rcases h4647 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p805 := by
    rcases h4652 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p806 := by
    rcases h4657 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p807 := by
    rcases h4662 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4556 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24631 (p796 p802 p804 p805 p806 p807 p808 p809 : Prop)
    (h21018 : (¬ p796) ∨ p802)
    (h4643 : p804 ∨ p809)
    (h4648 : p805 ∨ p809)
    (h4653 : p806 ∨ p809)
    (h4658 : p807 ∨ p809)
    (h4556 : p796 ∨ p802 ∨ (¬ p804) ∨ (¬ p805) ∨ (¬ p806) ∨ (¬ p807) ∨ (¬ p808)) : p809 ∨ (¬ p808) ∨ p802 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p809) := fun hu => hn (Or.inl hu)
  have u1 : p808 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p802) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : (¬ p796) := by
    rcases h21018 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : p804 := by
    rcases h4643 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p805 := by
    rcases h4648 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p806 := by
    rcases h4653 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p807 := by
    rcases h4658 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4556 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24632 (p796 p802 p804 p805 p806 p807 p808 p809 p810 p811 p812 p813 : Prop)
    (h24628 : p808 ∨ (¬ p811) ∨ p802 ∨ p796)
    (h24629 : p812 ∨ (¬ p808) ∨ p802 ∨ p796)
    (h24630 : p813 ∨ (¬ p808) ∨ p802)
    (h24631 : p809 ∨ (¬ p808) ∨ p802)
    (h4581 : p796 ∨ p802 ∨ (¬ p809) ∨ (¬ p810) ∨ (¬ p811) ∨ (¬ p812) ∨ (¬ p813))
    (h4644 : p804 ∨ p810)
    (h4649 : p805 ∨ p810)
    (h4654 : p806 ∨ p810)
    (h4659 : p807 ∨ p810)
    (h4556 : p796 ∨ p802 ∨ (¬ p804) ∨ (¬ p805) ∨ (¬ p806) ∨ (¬ p807) ∨ (¬ p808)) : (¬ p811) ∨ p796 ∨ p802 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p811 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p796) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p802) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p808 := by
    rcases h24628 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u2 q2)
    · exact False.elim (u1 q3)
  have u4 : p812 := by
    rcases h24629 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u2 q2)
    · exact False.elim (u1 q3)
  have u5 : p813 := by
    rcases h24630 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u2 q2)
  have u6 : p809 := by
    rcases h24631 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u2 q2)
  have u7 : (¬ p810) := by
    rcases h4581 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u6)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u5)
  have u8 : p804 := by
    rcases h4644 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p805 := by
    rcases h4649 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p806 := by
    rcases h4654 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p807 := by
    rcases h4659 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h4556 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u3)

theorem step24633 (p796 p802 p804 p805 p806 p807 p808 p811 : Prop)
    (h24632 : (¬ p811) ∨ p796 ∨ p802)
    (h4645 : p804 ∨ p811)
    (h4650 : p805 ∨ p811)
    (h4655 : p806 ∨ p811)
    (h4660 : p807 ∨ p811)
    (h4665 : p808 ∨ p811)
    (h4556 : p796 ∨ p802 ∨ (¬ p804) ∨ (¬ p805) ∨ (¬ p806) ∨ (¬ p807) ∨ (¬ p808)) : p796 ∨ p802 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p796) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p802) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p811) := by
    rcases h24632 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p804 := by
    rcases h4645 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : p805 := by
    rcases h4650 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p806 := by
    rcases h4655 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p807 := by
    rcases h4660 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p808 := by
    rcases h4665 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h4556 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24634 (p796 p802 : Prop)
    (h21018 : (¬ p796) ∨ p802)
    (h24633 : p796 ∨ p802) : p802 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p802) := fun hu => hn hu
  have u1 : (¬ p796) := by
    rcases h21018 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h24633 with q0 | q1
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)

theorem step24635 (p44 p48 p63 p69 p802 p1393 : Prop)
    (h24634 : p802)
    (h11773 : (¬ p48) ∨ (¬ p63) ∨ (¬ p69))
    (h17599 : (¬ p44) ∨ (¬ p63) ∨ (¬ p69) ∨ (¬ p802) ∨ (¬ p1393))
    (h21322 : p48 ∨ p44) : (¬ p69) ∨ (¬ p1393) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p802 := by
    exact h24634
  have u4 : (¬ p48) := by
    rcases h11773 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u0)
  have u5 : (¬ p44) := by
    rcases h17599 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u0)
    · exact False.elim (q3 u3)
    · exact False.elim (q4 u1)
  rcases h21322 with q0 | q1
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)

theorem step24636 (p3 p47 p71 p229 p424 p534 p543 p727 p737 p840 p940 p1584 : Prop)
    (h10634 : (¬ p737) ∨ (¬ p840) ∨ (¬ p1584))
    (h17704 : (¬ p3) ∨ (¬ p71) ∨ (¬ p534) ∨ (¬ p840) ∨ (¬ p1584))
    (h23055 : p727 ∨ p737)
    (h21095 : p940 ∨ p534)
    (h18605 : (¬ p47) ∨ (¬ p229) ∨ (¬ p424) ∨ (¬ p543) ∨ (¬ p727) ∨ (¬ p940)) : (¬ p1584) ∨ (¬ p840) ∨ (¬ p3) ∨ (¬ p229) ∨ (¬ p543) ∨ (¬ p47) ∨ (¬ p71) ∨ (¬ p424) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p543 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p737) := by
    rcases h10634 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u1)
    · exact False.elim (q2 u0)
  have u9 : (¬ p534) := by
    rcases h17704 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u2)
    · exact False.elim (q1 u6)
    · exact q2
    · exact False.elim (q3 u1)
    · exact False.elim (q4 u0)
  have u10 : p727 := by
    rcases h23055 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u11 : p940 := by
    rcases h21095 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h18605 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)

theorem step24637 (p323 p324 p332 p333 p334 p335 p336 p340 : Prop)
    (h1802 : p332 ∨ p340)
    (h1807 : p333 ∨ p340)
    (h1812 : p334 ∨ p340)
    (h1817 : p335 ∨ p340)
    (h1822 : p336 ∨ p340)
    (h1701 : p323 ∨ p324 ∨ (¬ p332) ∨ (¬ p333) ∨ (¬ p334) ∨ (¬ p335) ∨ (¬ p336)) : p340 ∨ p324 ∨ p323 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p340) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p324) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p323) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p332 := by
    rcases h1802 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p333 := by
    rcases h1807 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p334 := by
    rcases h1812 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p335 := by
    rcases h1817 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p336 := by
    rcases h1822 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1701 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24638 (p323 p324 p332 p337 p338 p339 p340 p341 : Prop)
    (h24637 : p340 ∨ p324 ∨ p323)
    (h1799 : p332 ∨ p337)
    (h1800 : p332 ∨ p338)
    (h1801 : p332 ∨ p339)
    (h1803 : p332 ∨ p341)
    (h1726 : p323 ∨ p324 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341)) : p332 ∨ p324 ∨ p323 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p332) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p324) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p323) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p340 := by
    rcases h24637 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p337 := by
    rcases h1799 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p338 := by
    rcases h1800 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p339 := by
    rcases h1801 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p341 := by
    rcases h1803 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1726 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24639 (p323 p324 p334 p337 p338 p339 p340 p341 : Prop)
    (h24637 : p340 ∨ p324 ∨ p323)
    (h1809 : p334 ∨ p337)
    (h1810 : p334 ∨ p338)
    (h1811 : p334 ∨ p339)
    (h1813 : p334 ∨ p341)
    (h1726 : p323 ∨ p324 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341)) : p334 ∨ p324 ∨ p323 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p334) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p324) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p323) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p340 := by
    rcases h24637 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p337 := by
    rcases h1809 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p338 := by
    rcases h1810 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p339 := by
    rcases h1811 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p341 := by
    rcases h1813 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1726 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24640 (p323 p324 p335 p337 p338 p339 p340 p341 : Prop)
    (h24637 : p340 ∨ p324 ∨ p323)
    (h1814 : p335 ∨ p337)
    (h1815 : p335 ∨ p338)
    (h1816 : p335 ∨ p339)
    (h1818 : p335 ∨ p341)
    (h1726 : p323 ∨ p324 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341)) : p335 ∨ p324 ∨ p323 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p335) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p324) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p323) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p340 := by
    rcases h24637 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p337 := by
    rcases h1814 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p338 := by
    rcases h1815 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p339 := by
    rcases h1816 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p341 := by
    rcases h1818 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1726 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24641 (p323 p324 p336 p337 p338 p339 p340 p341 : Prop)
    (h24637 : p340 ∨ p324 ∨ p323)
    (h1819 : p336 ∨ p337)
    (h1820 : p336 ∨ p338)
    (h1821 : p336 ∨ p339)
    (h1823 : p336 ∨ p341)
    (h1726 : p323 ∨ p324 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341)) : p336 ∨ p324 ∨ p323 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p336) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p324) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p323) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p340 := by
    rcases h24637 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p337 := by
    rcases h1819 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p338 := by
    rcases h1820 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p339 := by
    rcases h1821 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p341 := by
    rcases h1823 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1726 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24642 (p323 p324 p332 p333 p334 p335 p336 p337 p338 p339 p340 p341 : Prop)
    (h24637 : p340 ∨ p324 ∨ p323)
    (h24638 : p332 ∨ p324 ∨ p323)
    (h24639 : p334 ∨ p324 ∨ p323)
    (h24640 : p335 ∨ p324 ∨ p323)
    (h24641 : p336 ∨ p324 ∨ p323)
    (h1701 : p323 ∨ p324 ∨ (¬ p332) ∨ (¬ p333) ∨ (¬ p334) ∨ (¬ p335) ∨ (¬ p336))
    (h1804 : p333 ∨ p337)
    (h1805 : p333 ∨ p338)
    (h1806 : p333 ∨ p339)
    (h1808 : p333 ∨ p341)
    (h1726 : p323 ∨ p324 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341)) : p324 ∨ p323 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p324) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p323) := fun hu => hn (Or.inr hu)
  have u2 : p340 := by
    rcases h24637 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p332 := by
    rcases h24638 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p334 := by
    rcases h24639 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p335 := by
    rcases h24640 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p336 := by
    rcases h24641 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p333) := by
    rcases h1701 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u3)
    · exact q3
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u6)
  have u8 : p337 := by
    rcases h1804 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p338 := by
    rcases h1805 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p339 := by
    rcases h1806 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p341 := by
    rcases h1808 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h1726 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u11)

theorem step24643 (p207 p213 p214 p215 p216 p217 p218 p222 : Prop)
    (h1150 : p214 ∨ p222)
    (h1155 : p215 ∨ p222)
    (h1160 : p216 ∨ p222)
    (h1165 : p217 ∨ p222)
    (h1170 : p218 ∨ p222)
    (h1056 : p207 ∨ p213 ∨ (¬ p214) ∨ (¬ p215) ∨ (¬ p216) ∨ (¬ p217) ∨ (¬ p218)) : p222 ∨ p213 ∨ p207 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p222) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p213) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p207) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p214 := by
    rcases h1150 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p215 := by
    rcases h1155 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p216 := by
    rcases h1160 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p217 := by
    rcases h1165 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p218 := by
    rcases h1170 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1056 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24644 (p207 p213 p214 p219 p220 p221 p222 p223 : Prop)
    (h24643 : p222 ∨ p213 ∨ p207)
    (h1147 : p214 ∨ p219)
    (h1148 : p214 ∨ p220)
    (h1149 : p214 ∨ p221)
    (h1151 : p214 ∨ p223)
    (h1081 : p207 ∨ p213 ∨ (¬ p219) ∨ (¬ p220) ∨ (¬ p221) ∨ (¬ p222) ∨ (¬ p223)) : p214 ∨ p213 ∨ p207 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p214) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p213) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p207) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p222 := by
    rcases h24643 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p219 := by
    rcases h1147 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p220 := by
    rcases h1148 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p221 := by
    rcases h1149 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p223 := by
    rcases h1151 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1081 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24645 (p207 p213 p215 p219 p220 p221 p222 p223 : Prop)
    (h24643 : p222 ∨ p213 ∨ p207)
    (h1152 : p215 ∨ p219)
    (h1153 : p215 ∨ p220)
    (h1154 : p215 ∨ p221)
    (h1156 : p215 ∨ p223)
    (h1081 : p207 ∨ p213 ∨ (¬ p219) ∨ (¬ p220) ∨ (¬ p221) ∨ (¬ p222) ∨ (¬ p223)) : p215 ∨ p213 ∨ p207 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p215) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p213) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p207) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p222 := by
    rcases h24643 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p219 := by
    rcases h1152 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p220 := by
    rcases h1153 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p221 := by
    rcases h1154 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p223 := by
    rcases h1156 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1081 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24646 (p207 p213 p216 p219 p220 p221 p222 p223 : Prop)
    (h24643 : p222 ∨ p213 ∨ p207)
    (h1157 : p216 ∨ p219)
    (h1158 : p216 ∨ p220)
    (h1159 : p216 ∨ p221)
    (h1161 : p216 ∨ p223)
    (h1081 : p207 ∨ p213 ∨ (¬ p219) ∨ (¬ p220) ∨ (¬ p221) ∨ (¬ p222) ∨ (¬ p223)) : p216 ∨ p213 ∨ p207 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p216) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p213) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p207) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p222 := by
    rcases h24643 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p219 := by
    rcases h1157 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p220 := by
    rcases h1158 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p221 := by
    rcases h1159 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p223 := by
    rcases h1161 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1081 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24647 (p207 p213 p217 p219 p220 p221 p222 p223 : Prop)
    (h24643 : p222 ∨ p213 ∨ p207)
    (h1162 : p217 ∨ p219)
    (h1163 : p217 ∨ p220)
    (h1164 : p217 ∨ p221)
    (h1166 : p217 ∨ p223)
    (h1081 : p207 ∨ p213 ∨ (¬ p219) ∨ (¬ p220) ∨ (¬ p221) ∨ (¬ p222) ∨ (¬ p223)) : p217 ∨ p213 ∨ p207 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p217) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p213) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p207) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p222 := by
    rcases h24643 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p219 := by
    rcases h1162 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p220 := by
    rcases h1163 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p221 := by
    rcases h1164 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p223 := by
    rcases h1166 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1081 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24648 (p6 p102 p104 p124 p142 p167 p207 p213 p214 p215 p216 p217 p218 p219 p220 p221 p222 p223 : Prop)
    (h21934 : p104 ∨ p102)
    (h9303 : p102 ∨ (¬ p124) ∨ (¬ p207))
    (h18811 : (¬ p104) ∨ (¬ p124) ∨ (¬ p142) ∨ (¬ p167) ∨ (¬ p213))
    (h24643 : p222 ∨ p213 ∨ p207)
    (h24644 : p214 ∨ p213 ∨ p207)
    (h24645 : p215 ∨ p213 ∨ p207)
    (h24646 : p216 ∨ p213 ∨ p207)
    (h24647 : p217 ∨ p213 ∨ p207)
    (h1061 : p6 ∨ p213 ∨ (¬ p214) ∨ (¬ p215) ∨ (¬ p216) ∨ (¬ p217) ∨ (¬ p218))
    (h1167 : p218 ∨ p219)
    (h1168 : p218 ∨ p220)
    (h1169 : p218 ∨ p221)
    (h1171 : p218 ∨ p223)
    (h1081 : p207 ∨ p213 ∨ (¬ p219) ∨ (¬ p220) ∨ (¬ p221) ∨ (¬ p222) ∨ (¬ p223)) : (¬ p124) ∨ (¬ p167) ∨ p102 ∨ p6 ∨ (¬ p142) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p102) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p104 := by
    rcases h21934 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : (¬ p207) := by
    rcases h9303 with q0 | q1 | q2
    · exact False.elim (u2 q0)
    · exact False.elim (q1 u0)
    · exact q2
  have u7 : (¬ p213) := by
    rcases h18811 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u5)
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u1)
    · exact q4
  have u8 : p222 := by
    rcases h24643 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u7 q1)
    · exact False.elim (u6 q2)
  have u9 : p214 := by
    rcases h24644 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u7 q1)
    · exact False.elim (u6 q2)
  have u10 : p215 := by
    rcases h24645 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u7 q1)
    · exact False.elim (u6 q2)
  have u11 : p216 := by
    rcases h24646 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u7 q1)
    · exact False.elim (u6 q2)
  have u12 : p217 := by
    rcases h24647 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u7 q1)
    · exact False.elim (u6 q2)
  have u13 : (¬ p218) := by
    rcases h1061 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u7 q1)
    · exact False.elim (q2 u9)
    · exact False.elim (q3 u10)
    · exact False.elim (q4 u11)
    · exact False.elim (q5 u12)
    · exact q6
  have u14 : p219 := by
    rcases h1167 with q0 | q1
    · exact False.elim (u13 q0)
    · exact q1
  have u15 : p220 := by
    rcases h1168 with q0 | q1
    · exact False.elim (u13 q0)
    · exact q1
  have u16 : p221 := by
    rcases h1169 with q0 | q1
    · exact False.elim (u13 q0)
    · exact q1
  have u17 : p223 := by
    rcases h1171 with q0 | q1
    · exact False.elim (u13 q0)
    · exact q1
  rcases h1081 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u14)
  · exact False.elim (q3 u15)
  · exact False.elim (q4 u16)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u17)

theorem step24649 (p3 p19 p229 p423 p532 p996 p1000 p1001 p1141 p1206 p1325 p1333 p1465 : Prop)
    (h21656 : p1325 ∨ p1333)
    (h12383 : (¬ p1001) ∨ p1325 ∨ (¬ p1465))
    (h19125 : (¬ p19) ∨ (¬ p1141) ∨ (¬ p1333) ∨ (¬ p1465))
    (h24391 : p1000 ∨ p1001 ∨ p996)
    (h20723 : p423 ∨ p1141)
    (h18630 : (¬ p3) ∨ (¬ p229) ∨ (¬ p423) ∨ (¬ p532) ∨ (¬ p1000) ∨ (¬ p1206) ∨ (¬ p1333)) : (¬ p1465) ∨ p1325 ∨ (¬ p532) ∨ (¬ p3) ∨ p996 ∨ (¬ p229) ∨ (¬ p19) ∨ (¬ p1206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p996) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1333 := by
    rcases h21656 with q0 | q1
    · exact False.elim (u1 q0)
    · exact q1
  have u9 : (¬ p1001) := by
    rcases h12383 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u0)
  have u10 : (¬ p1141) := by
    rcases h19125 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u6)
    · exact q1
    · exact False.elim (q2 u8)
    · exact False.elim (q3 u0)
  have u11 : p1000 := by
    rcases h24391 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u9 q1)
    · exact False.elim (u4 q2)
  have u12 : p423 := by
    rcases h20723 with q0 | q1
    · exact q0
    · exact False.elim (u10 q1)
  rcases h18630 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u12)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u8)

theorem step24650 (p3 p13 p19 p47 p63 p71 p125 p161 p195 p227 p229 p303 p304 p350 p362 p368 p382 p406 p420 p423 p532 p533 p537 p581 p621 p636 p928 p961 p980 p996 p1035 p1084 p1116 p1140 p1206 p1225 p1249 p1252 p1255 p1256 p1272 p1325 p1333 p1452 p1465 p1489 p1493 : Prop)
    (h1953 : (¬ p125) ∨ (¬ p362))
    (h18607 : (¬ p13) ∨ (¬ p63) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p928) ∨ (¬ p961) ∨ (¬ p1116))
    (h21374 : p368 ∨ p125)
    (h21044 : p961 ∨ p227)
    (h16176 : (¬ p303) ∨ (¬ p304) ∨ (¬ p350) ∨ (¬ p368) ∨ (¬ p406))
    (h18922 : (¬ p227) ∨ (¬ p304) ∨ (¬ p980) ∨ (¬ p1452))
    (h21752 : p382 ∨ p406)
    (h21329 : p1452 ∨ p532)
    (h18606 : (¬ p63) ∨ (¬ p382) ∨ (¬ p533) ∨ (¬ p537) ∨ (¬ p621) ∨ (¬ p928) ∨ (¬ p1325))
    (h21972 : (¬ p1225) ∨ (¬ p532) ∨ (¬ p1084) ∨ (¬ p636))
    (h21656 : p1325 ∨ p1333)
    (h21572 : p161 ∨ p1225)
    (h19104 : (¬ p532) ∨ (¬ p581) ∨ (¬ p1249) ∨ (¬ p1333) ∨ (¬ p1493))
    (h22624 : p1272 ∨ p1249)
    (h13225 : (¬ p161) ∨ (¬ p1272) ∨ p1489)
    (h24649 : (¬ p1465) ∨ p1325 ∨ (¬ p532) ∨ (¬ p3) ∨ p996 ∨ (¬ p229) ∨ (¬ p19) ∨ (¬ p1206))
    (h21566 : p1465 ∨ p1035)
    (h10814 : (¬ p1035) ∨ (¬ p1255) ∨ (¬ p1489))
    (h16704 : (¬ p195) ∨ (¬ p1035) ∨ (¬ p1140) ∨ (¬ p1252) ∨ (¬ p1489))
    (h19114 : (¬ p3) ∨ (¬ p71) ∨ (¬ p229) ∨ (¬ p423) ∨ (¬ p1035))
    (h22882 : p1252 ∨ p1255 ∨ p1256)
    (h11274 : (¬ p47) ∨ p423 ∨ (¬ p1256)) : (¬ p362) ∨ (¬ p1493) ∨ (¬ p303) ∨ (¬ p533) ∨ (¬ p980) ∨ (¬ p928) ∨ (¬ p350) ∨ (¬ p1116) ∨ (¬ p537) ∨ (¬ p420) ∨ (¬ p1140) ∨ (¬ p3) ∨ (¬ p1084) ∨ (¬ p13) ∨ p996 ∨ (¬ p229) ∨ (¬ p621) ∨ (¬ p71) ∨ (¬ p636) ∨ (¬ p19) ∨ (¬ p581) ∨ (¬ p1206) ∨ (¬ p47) ∨ (¬ p63) ∨ (¬ p304) ∨ (¬ p195) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1493 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : (¬ p996) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))
  have u15 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))
  have u16 : p621 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))
  have u17 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))))
  have u18 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))))
  have u19 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))))))
  have u20 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))))))
  have u21 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))))))))
  have u22 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))))))))
  have u23 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))))))))))
  have u24 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))))))))))
  have u25 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))))))))))))))))
  have u26 : (¬ p125) := by
    rcases h1953 with q0 | q1
    · exact q0
    · exact False.elim (q1 u0)
  have u27 : (¬ p961) := by
    rcases h18607 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u13)
    · exact False.elim (q1 u23)
    · exact False.elim (q2 u0)
    · exact False.elim (q3 u9)
    · exact False.elim (q4 u5)
    · exact q5
    · exact False.elim (q6 u7)
  have u28 : p368 := by
    rcases h21374 with q0 | q1
    · exact q0
    · exact False.elim (u26 q1)
  have u29 : p227 := by
    rcases h21044 with q0 | q1
    · exact False.elim (u27 q0)
    · exact q1
  have u30 : (¬ p406) := by
    rcases h16176 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u2)
    · exact False.elim (q1 u24)
    · exact False.elim (q2 u6)
    · exact False.elim (q3 u28)
    · exact q4
  have u31 : (¬ p1452) := by
    rcases h18922 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u29)
    · exact False.elim (q1 u24)
    · exact False.elim (q2 u4)
    · exact q3
  have u32 : p382 := by
    rcases h21752 with q0 | q1
    · exact q0
    · exact False.elim (u30 q1)
  have u33 : p532 := by
    rcases h21329 with q0 | q1
    · exact False.elim (u31 q0)
    · exact q1
  have u34 : (¬ p1325) := by
    rcases h18606 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u23)
    · exact False.elim (q1 u32)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u8)
    · exact False.elim (q4 u16)
    · exact False.elim (q5 u5)
    · exact q6
  have u35 : (¬ p1225) := by
    rcases h21972 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u33)
    · exact False.elim (q2 u12)
    · exact False.elim (q3 u18)
  have u36 : p1333 := by
    rcases h21656 with q0 | q1
    · exact False.elim (u34 q0)
    · exact q1
  have u37 : p161 := by
    rcases h21572 with q0 | q1
    · exact q0
    · exact False.elim (u35 q1)
  have u38 : (¬ p1249) := by
    rcases h19104 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u33)
    · exact False.elim (q1 u20)
    · exact q2
    · exact False.elim (q3 u36)
    · exact False.elim (q4 u1)
  have u39 : p1272 := by
    rcases h22624 with q0 | q1
    · exact q0
    · exact False.elim (u38 q1)
  have u40 : p1489 := by
    rcases h13225 with q0 | q1 | q2
    · exact False.elim (q0 u37)
    · exact False.elim (q1 u39)
    · exact q2
  have u41 : (¬ p1465) := by
    rcases h24649 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
    · exact q0
    · exact False.elim (u34 q1)
    · exact False.elim (q2 u33)
    · exact False.elim (q3 u11)
    · exact False.elim (u14 q4)
    · exact False.elim (q5 u15)
    · exact False.elim (q6 u19)
    · exact False.elim (q7 u21)
  have u42 : p1035 := by
    rcases h21566 with q0 | q1
    · exact False.elim (u41 q0)
    · exact q1
  have u43 : (¬ p1255) := by
    rcases h10814 with q0 | q1 | q2
    · exact False.elim (q0 u42)
    · exact q1
    · exact False.elim (q2 u40)
  have u44 : (¬ p1252) := by
    rcases h16704 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u25)
    · exact False.elim (q1 u42)
    · exact False.elim (q2 u10)
    · exact q3
    · exact False.elim (q4 u40)
  have u45 : (¬ p423) := by
    rcases h19114 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u11)
    · exact False.elim (q1 u17)
    · exact False.elim (q2 u15)
    · exact q3
    · exact False.elim (q4 u42)
  have u46 : p1256 := by
    rcases h22882 with q0 | q1 | q2
    · exact False.elim (u44 q0)
    · exact False.elim (u43 q1)
    · exact q2
  rcases h11274 with q0 | q1 | q2
  · exact False.elim (q0 u22)
  · exact False.elim (u45 q1)
  · exact False.elim (q2 u46)

theorem step24651 (p3 p41 p45 p47 p63 p71 p195 p229 p423 p980 p1035 p1140 p1249 p1252 p1253 p1255 p1256 p1273 p1489 p1508 : Prop)
    (h6739 : (¬ p41) ∨ (¬ p45))
    (h22129 : p45 ∨ p47)
    (h19114 : (¬ p3) ∨ (¬ p71) ∨ (¬ p229) ∨ (¬ p423) ∨ (¬ p1035))
    (h11274 : (¬ p47) ∨ p423 ∨ (¬ p1256))
    (h23500 : p1253 ∨ p1256)
    (h18603 : (¬ p41) ∨ (¬ p195) ∨ (¬ p1140) ∨ (¬ p1249) ∨ (¬ p1253))
    (h21525 : p1273 ∨ p1249)
    (h18599 : (¬ p63) ∨ (¬ p980) ∨ (¬ p1273) ∨ (¬ p1508))
    (h21548 : p1508 ∨ p1489)
    (h14971 : (¬ p1035) ∨ (¬ p1255) ∨ p1508)
    (h16704 : (¬ p195) ∨ (¬ p1035) ∨ (¬ p1140) ∨ (¬ p1252) ∨ (¬ p1489))
    (h22882 : p1252 ∨ p1255 ∨ p1256) : (¬ p1035) ∨ (¬ p980) ∨ (¬ p1140) ∨ (¬ p3) ∨ (¬ p229) ∨ (¬ p71) ∨ (¬ p41) ∨ (¬ p63) ∨ (¬ p195) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p45) := by
    rcases h6739 with q0 | q1
    · exact False.elim (q0 u6)
    · exact q1
  have u10 : p47 := by
    rcases h22129 with q0 | q1
    · exact False.elim (u9 q0)
    · exact q1
  have u11 : (¬ p423) := by
    rcases h19114 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u3)
    · exact False.elim (q1 u5)
    · exact False.elim (q2 u4)
    · exact q3
    · exact False.elim (q4 u0)
  have u12 : (¬ p1256) := by
    rcases h11274 with q0 | q1 | q2
    · exact False.elim (q0 u10)
    · exact False.elim (u11 q1)
    · exact q2
  have u13 : p1253 := by
    rcases h23500 with q0 | q1
    · exact q0
    · exact False.elim (u12 q1)
  have u14 : (¬ p1249) := by
    rcases h18603 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u6)
    · exact False.elim (q1 u8)
    · exact False.elim (q2 u2)
    · exact q3
    · exact False.elim (q4 u13)
  have u15 : p1273 := by
    rcases h21525 with q0 | q1
    · exact q0
    · exact False.elim (u14 q1)
  have u16 : (¬ p1508) := by
    rcases h18599 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u7)
    · exact False.elim (q1 u1)
    · exact False.elim (q2 u15)
    · exact q3
  have u17 : p1489 := by
    rcases h21548 with q0 | q1
    · exact False.elim (u16 q0)
    · exact q1
  have u18 : (¬ p1255) := by
    rcases h14971 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (u16 q2)
  have u19 : (¬ p1252) := by
    rcases h16704 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u8)
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u2)
    · exact q3
    · exact False.elim (q4 u17)
  rcases h22882 with q0 | q1 | q2
  · exact False.elim (u19 q0)
  · exact False.elim (u18 q1)
  · exact False.elim (u12 q2)

theorem step24652 (p268 p301 p303 p364 p368 p406 : Prop)
    (h2332 : (¬ p303) ∨ (¬ p364) ∨ (¬ p406))
    (h18085 : (¬ p268) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p368) ∨ (¬ p406))
    (h21352 : p368 ∨ p364) : (¬ p303) ∨ (¬ p406) ∨ (¬ p301) ∨ (¬ p268) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p268 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p364) := by
    rcases h2332 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (q2 u1)
  have u5 : (¬ p368) := by
    rcases h18085 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u3)
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u0)
    · exact q3
    · exact False.elim (q4 u1)
  rcases h21352 with q0 | q1
  · exact False.elim (u5 q0)
  · exact False.elim (u4 q1)

theorem step24653 (p494 p500 p502 p503 p504 p505 p506 p511 : Prop)
    (h2831 : p502 ∨ p511)
    (h2836 : p503 ∨ p511)
    (h2841 : p504 ∨ p511)
    (h2846 : p505 ∨ p511)
    (h2851 : p506 ∨ p511)
    (h2730 : p494 ∨ p500 ∨ (¬ p502) ∨ (¬ p503) ∨ (¬ p504) ∨ (¬ p505) ∨ (¬ p506)) : p511 ∨ p494 ∨ p500 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p511) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p494) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p500) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p502 := by
    rcases h2831 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p503 := by
    rcases h2836 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p504 := by
    rcases h2841 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p505 := by
    rcases h2846 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p506 := by
    rcases h2851 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2730 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24654 (p494 p500 p502 p503 p504 p505 p506 p507 : Prop)
    (h2827 : p502 ∨ p507)
    (h2832 : p503 ∨ p507)
    (h2837 : p504 ∨ p507)
    (h2842 : p505 ∨ p507)
    (h2847 : p506 ∨ p507)
    (h2730 : p494 ∨ p500 ∨ (¬ p502) ∨ (¬ p503) ∨ (¬ p504) ∨ (¬ p505) ∨ (¬ p506)) : p507 ∨ p494 ∨ p500 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p507) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p494) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p500) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p502 := by
    rcases h2827 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p503 := by
    rcases h2832 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p504 := by
    rcases h2837 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p505 := by
    rcases h2842 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p506 := by
    rcases h2847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2730 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24655 (p494 p500 p502 p503 p504 p505 p506 p508 : Prop)
    (h2828 : p502 ∨ p508)
    (h2833 : p503 ∨ p508)
    (h2838 : p504 ∨ p508)
    (h2843 : p505 ∨ p508)
    (h2848 : p506 ∨ p508)
    (h2730 : p494 ∨ p500 ∨ (¬ p502) ∨ (¬ p503) ∨ (¬ p504) ∨ (¬ p505) ∨ (¬ p506)) : p508 ∨ p494 ∨ p500 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p508) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p494) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p500) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p502 := by
    rcases h2828 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p503 := by
    rcases h2833 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p504 := by
    rcases h2838 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p505 := by
    rcases h2843 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p506 := by
    rcases h2848 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2730 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24656 (p494 p500 p502 p503 p504 p505 p506 p509 : Prop)
    (h2829 : p502 ∨ p509)
    (h2834 : p503 ∨ p509)
    (h2839 : p504 ∨ p509)
    (h2844 : p505 ∨ p509)
    (h2849 : p506 ∨ p509)
    (h2730 : p494 ∨ p500 ∨ (¬ p502) ∨ (¬ p503) ∨ (¬ p504) ∨ (¬ p505) ∨ (¬ p506)) : p509 ∨ p494 ∨ p500 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p509) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p494) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p500) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p502 := by
    rcases h2829 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p503 := by
    rcases h2834 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p504 := by
    rcases h2839 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p505 := by
    rcases h2844 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p506 := by
    rcases h2849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2730 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24657 (p494 p500 p502 p503 p504 p505 p506 p507 p508 p509 p510 p511 : Prop)
    (h2755 : p494 ∨ p500 ∨ (¬ p507) ∨ (¬ p508) ∨ (¬ p509) ∨ (¬ p510) ∨ (¬ p511))
    (h2830 : p502 ∨ p510)
    (h2835 : p503 ∨ p510)
    (h2840 : p504 ∨ p510)
    (h2845 : p505 ∨ p510)
    (h2850 : p506 ∨ p510)
    (h2730 : p494 ∨ p500 ∨ (¬ p502) ∨ (¬ p503) ∨ (¬ p504) ∨ (¬ p505) ∨ (¬ p506)) : (¬ p509) ∨ (¬ p511) ∨ p500 ∨ p494 ∨ (¬ p507) ∨ (¬ p508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p509 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p511 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p500) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p494) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p507 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p510) := by
    rcases h2755 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u0)
    · exact q5
    · exact False.elim (q6 u1)
  have u7 : p502 := by
    rcases h2830 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p503 := by
    rcases h2835 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p504 := by
    rcases h2840 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p505 := by
    rcases h2845 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p506 := by
    rcases h2850 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h2730 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step24658 (p494 p500 p507 p508 p509 p511 : Prop)
    (h24653 : p511 ∨ p494 ∨ p500)
    (h24654 : p507 ∨ p494 ∨ p500)
    (h24655 : p508 ∨ p494 ∨ p500)
    (h24656 : p509 ∨ p494 ∨ p500)
    (h24657 : (¬ p509) ∨ (¬ p511) ∨ p500 ∨ p494 ∨ (¬ p507) ∨ (¬ p508)) : p494 ∨ p500 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p494) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p500) := fun hu => hn (Or.inr hu)
  have u2 : p511 := by
    rcases h24653 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p507 := by
    rcases h24654 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p508 := by
    rcases h24655 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p509 := by
    rcases h24656 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h24657 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step24659 (p494 p495 p500 p502 p503 p504 p505 p506 p510 : Prop)
    (h24658 : p494 ∨ p500)
    (h17338 : (¬ p494) ∨ (¬ p495) ∨ p500)
    (h2830 : p502 ∨ p510)
    (h2835 : p503 ∨ p510)
    (h2840 : p504 ∨ p510)
    (h2845 : p505 ∨ p510)
    (h2850 : p506 ∨ p510)
    (h2740 : p495 ∨ p500 ∨ (¬ p502) ∨ (¬ p503) ∨ (¬ p504) ∨ (¬ p505) ∨ (¬ p506)) : p510 ∨ p500 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p510) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p500) := fun hu => hn (Or.inr hu)
  have u2 : p494 := by
    rcases h24658 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u3 : (¬ p495) := by
    rcases h17338 with q0 | q1 | q2
    · exact False.elim (q0 u2)
    · exact q1
    · exact False.elim (u1 q2)
  have u4 : p502 := by
    rcases h2830 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p503 := by
    rcases h2835 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p504 := by
    rcases h2840 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p505 := by
    rcases h2845 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p506 := by
    rcases h2850 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2740 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u8)

theorem step24660 (p494 p495 p500 p502 p503 p504 p505 p506 p511 : Prop)
    (h24658 : p494 ∨ p500)
    (h17338 : (¬ p494) ∨ (¬ p495) ∨ p500)
    (h2831 : p502 ∨ p511)
    (h2836 : p503 ∨ p511)
    (h2841 : p504 ∨ p511)
    (h2846 : p505 ∨ p511)
    (h2851 : p506 ∨ p511)
    (h2740 : p495 ∨ p500 ∨ (¬ p502) ∨ (¬ p503) ∨ (¬ p504) ∨ (¬ p505) ∨ (¬ p506)) : p511 ∨ p500 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p511) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p500) := fun hu => hn (Or.inr hu)
  have u2 : p494 := by
    rcases h24658 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u3 : (¬ p495) := by
    rcases h17338 with q0 | q1 | q2
    · exact False.elim (q0 u2)
    · exact q1
    · exact False.elim (u1 q2)
  have u4 : p502 := by
    rcases h2831 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p503 := by
    rcases h2836 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p504 := by
    rcases h2841 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p505 := by
    rcases h2846 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p506 := by
    rcases h2851 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2740 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u8)

theorem step24661 (p494 p495 p500 p502 p503 p504 p505 p506 p507 : Prop)
    (h24658 : p494 ∨ p500)
    (h17338 : (¬ p494) ∨ (¬ p495) ∨ p500)
    (h2827 : p502 ∨ p507)
    (h2832 : p503 ∨ p507)
    (h2837 : p504 ∨ p507)
    (h2842 : p505 ∨ p507)
    (h2847 : p506 ∨ p507)
    (h2740 : p495 ∨ p500 ∨ (¬ p502) ∨ (¬ p503) ∨ (¬ p504) ∨ (¬ p505) ∨ (¬ p506)) : p507 ∨ p500 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p507) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p500) := fun hu => hn (Or.inr hu)
  have u2 : p494 := by
    rcases h24658 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u3 : (¬ p495) := by
    rcases h17338 with q0 | q1 | q2
    · exact False.elim (q0 u2)
    · exact q1
    · exact False.elim (u1 q2)
  have u4 : p502 := by
    rcases h2827 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p503 := by
    rcases h2832 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p504 := by
    rcases h2837 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p505 := by
    rcases h2842 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p506 := by
    rcases h2847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2740 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u8)

theorem step24662 (p494 p495 p500 p502 p503 p504 p505 p506 p508 : Prop)
    (h24658 : p494 ∨ p500)
    (h17338 : (¬ p494) ∨ (¬ p495) ∨ p500)
    (h2828 : p502 ∨ p508)
    (h2833 : p503 ∨ p508)
    (h2838 : p504 ∨ p508)
    (h2843 : p505 ∨ p508)
    (h2848 : p506 ∨ p508)
    (h2740 : p495 ∨ p500 ∨ (¬ p502) ∨ (¬ p503) ∨ (¬ p504) ∨ (¬ p505) ∨ (¬ p506)) : p508 ∨ p500 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p508) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p500) := fun hu => hn (Or.inr hu)
  have u2 : p494 := by
    rcases h24658 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u3 : (¬ p495) := by
    rcases h17338 with q0 | q1 | q2
    · exact False.elim (q0 u2)
    · exact q1
    · exact False.elim (u1 q2)
  have u4 : p502 := by
    rcases h2828 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p503 := by
    rcases h2833 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p504 := by
    rcases h2838 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p505 := by
    rcases h2843 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p506 := by
    rcases h2848 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2740 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u8)

theorem step24663 (p495 p500 p502 p503 p504 p505 p506 p507 p508 p509 p510 p511 : Prop)
    (h2765 : p495 ∨ p500 ∨ (¬ p507) ∨ (¬ p508) ∨ (¬ p509) ∨ (¬ p510) ∨ (¬ p511))
    (h2829 : p502 ∨ p509)
    (h2834 : p503 ∨ p509)
    (h2839 : p504 ∨ p509)
    (h2844 : p505 ∨ p509)
    (h2849 : p506 ∨ p509)
    (h2740 : p495 ∨ p500 ∨ (¬ p502) ∨ (¬ p503) ∨ (¬ p504) ∨ (¬ p505) ∨ (¬ p506)) : (¬ p508) ∨ p500 ∨ p495 ∨ (¬ p511) ∨ (¬ p510) ∨ (¬ p507) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p500) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p511 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p510 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p507 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p509) := by
    rcases h2765 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u0)
    · exact q4
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u3)
  have u7 : p502 := by
    rcases h2829 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p503 := by
    rcases h2834 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p504 := by
    rcases h2839 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p505 := by
    rcases h2844 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p506 := by
    rcases h2849 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h2740 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step24664 (p494 p495 p500 p507 p508 p510 p511 : Prop)
    (h17338 : (¬ p494) ∨ (¬ p495) ∨ p500)
    (h24659 : p510 ∨ p500)
    (h24660 : p511 ∨ p500)
    (h24661 : p507 ∨ p500)
    (h24662 : p508 ∨ p500)
    (h24663 : (¬ p508) ∨ p500 ∨ p495 ∨ (¬ p511) ∨ (¬ p510) ∨ (¬ p507)) : (¬ p494) ∨ p500 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p500) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p495) := by
    rcases h17338 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (u1 q2)
  have u3 : p510 := by
    rcases h24659 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u4 : p511 := by
    rcases h24660 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p507 := by
    rcases h24661 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p508 := by
    rcases h24662 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h24663 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u6)
  · exact False.elim (u1 q1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)

theorem step24665 (p494 p500 : Prop)
    (h24658 : p494 ∨ p500)
    (h24664 : (¬ p494) ∨ p500) : p500 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p500) := fun hu => hn hu
  have u1 : p494 := by
    rcases h24658 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h24664 with q0 | q1
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)

theorem step24666 (p125 p227 p303 p304 p327 p328 p362 p383 p387 p419 : Prop)
    (h12617 : (¬ p303) ∨ (¬ p387))
    (h22618 : p383 ∨ p303)
    (h17692 : (¬ p304) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p419))
    (h12556 : (¬ p328) ∨ (¬ p387) ∨ (¬ p419))
    (h21038 : p125 ∨ p362)
    (h22444 : p327 ∨ p328)
    (h16232 : (¬ p125) ∨ (¬ p227) ∨ (¬ p327) ∨ (¬ p383) ∨ (¬ p419)) : (¬ p419) ∨ (¬ p304) ∨ (¬ p387) ∨ (¬ p227) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p303) := by
    rcases h12617 with q0 | q1
    · exact q0
    · exact False.elim (q1 u2)
  have u5 : p383 := by
    rcases h22618 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u6 : (¬ p362) := by
    rcases h17692 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u1)
    · exact q1
    · exact False.elim (q2 u2)
    · exact False.elim (q3 u0)
  have u7 : (¬ p328) := by
    rcases h12556 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u0)
  have u8 : p125 := by
    rcases h21038 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p327 := by
    rcases h22444 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h16232 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)

theorem step24668 (p224 p668 p670 p671 p672 p673 p674 p679 : Prop)
    (h3863 : p670 ∨ p679)
    (h3868 : p671 ∨ p679)
    (h3873 : p672 ∨ p679)
    (h3878 : p673 ∨ p679)
    (h3883 : p674 ∨ p679)
    (h3772 : p224 ∨ p668 ∨ (¬ p670) ∨ (¬ p671) ∨ (¬ p672) ∨ (¬ p673) ∨ (¬ p674)) : p679 ∨ p668 ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p679) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p668) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p670 := by
    rcases h3863 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p671 := by
    rcases h3868 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p672 := by
    rcases h3873 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p673 := by
    rcases h3878 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p674 := by
    rcases h3883 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3772 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24669 (p224 p668 p670 p675 p676 p677 p678 p679 : Prop)
    (h24668 : p679 ∨ p668 ∨ p224)
    (h3859 : p670 ∨ p675)
    (h3860 : p670 ∨ p676)
    (h3861 : p670 ∨ p677)
    (h3862 : p670 ∨ p678)
    (h3797 : p224 ∨ p668 ∨ (¬ p675) ∨ (¬ p676) ∨ (¬ p677) ∨ (¬ p678) ∨ (¬ p679)) : p670 ∨ p224 ∨ p668 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p670) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p668) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p679 := by
    rcases h24668 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u2 q1)
    · exact False.elim (u1 q2)
  have u4 : p675 := by
    rcases h3859 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p676 := by
    rcases h3860 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p677 := by
    rcases h3861 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p678 := by
    rcases h3862 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3797 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step24670 (p224 p668 p671 p675 p676 p677 p678 p679 : Prop)
    (h24668 : p679 ∨ p668 ∨ p224)
    (h3864 : p671 ∨ p675)
    (h3865 : p671 ∨ p676)
    (h3866 : p671 ∨ p677)
    (h3867 : p671 ∨ p678)
    (h3797 : p224 ∨ p668 ∨ (¬ p675) ∨ (¬ p676) ∨ (¬ p677) ∨ (¬ p678) ∨ (¬ p679)) : p671 ∨ p224 ∨ p668 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p671) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p668) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p679 := by
    rcases h24668 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u2 q1)
    · exact False.elim (u1 q2)
  have u4 : p675 := by
    rcases h3864 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p676 := by
    rcases h3865 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p677 := by
    rcases h3866 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p678 := by
    rcases h3867 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3797 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step24671 (p224 p668 p672 p675 p676 p677 p678 p679 : Prop)
    (h24668 : p679 ∨ p668 ∨ p224)
    (h3869 : p672 ∨ p675)
    (h3870 : p672 ∨ p676)
    (h3871 : p672 ∨ p677)
    (h3872 : p672 ∨ p678)
    (h3797 : p224 ∨ p668 ∨ (¬ p675) ∨ (¬ p676) ∨ (¬ p677) ∨ (¬ p678) ∨ (¬ p679)) : p672 ∨ p224 ∨ p668 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p672) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p668) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p679 := by
    rcases h24668 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u2 q1)
    · exact False.elim (u1 q2)
  have u4 : p675 := by
    rcases h3869 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p676 := by
    rcases h3870 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p677 := by
    rcases h3871 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p678 := by
    rcases h3872 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3797 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step24672 (p224 p668 p673 p675 p676 p677 p678 p679 : Prop)
    (h24668 : p679 ∨ p668 ∨ p224)
    (h3874 : p673 ∨ p675)
    (h3875 : p673 ∨ p676)
    (h3876 : p673 ∨ p677)
    (h3877 : p673 ∨ p678)
    (h3797 : p224 ∨ p668 ∨ (¬ p675) ∨ (¬ p676) ∨ (¬ p677) ∨ (¬ p678) ∨ (¬ p679)) : p673 ∨ p224 ∨ p668 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p673) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p668) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p679 := by
    rcases h24668 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u2 q1)
    · exact False.elim (u1 q2)
  have u4 : p675 := by
    rcases h3874 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p676 := by
    rcases h3875 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p677 := by
    rcases h3876 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p678 := by
    rcases h3877 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3797 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step24673 (p224 p668 p670 p671 p672 p673 p674 p675 p676 p677 p678 p679 : Prop)
    (h24668 : p679 ∨ p668 ∨ p224)
    (h24669 : p670 ∨ p224 ∨ p668)
    (h24670 : p671 ∨ p224 ∨ p668)
    (h24671 : p672 ∨ p224 ∨ p668)
    (h24672 : p673 ∨ p224 ∨ p668)
    (h3772 : p224 ∨ p668 ∨ (¬ p670) ∨ (¬ p671) ∨ (¬ p672) ∨ (¬ p673) ∨ (¬ p674))
    (h3879 : p674 ∨ p675)
    (h3880 : p674 ∨ p676)
    (h3881 : p674 ∨ p677)
    (h3882 : p674 ∨ p678)
    (h3797 : p224 ∨ p668 ∨ (¬ p675) ∨ (¬ p676) ∨ (¬ p677) ∨ (¬ p678) ∨ (¬ p679)) : p224 ∨ p668 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p224) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p668) := fun hu => hn (Or.inr hu)
  have u2 : p679 := by
    rcases h24668 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u3 : p670 := by
    rcases h24669 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p671 := by
    rcases h24670 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p672 := by
    rcases h24671 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p673 := by
    rcases h24672 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p674) := by
    rcases h3772 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u0 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p675 := by
    rcases h3879 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p676 := by
    rcases h3880 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p677 := by
    rcases h3881 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p678 := by
    rcases h3882 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h3797 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u2)

theorem step24674 (p4 p125 p224 p227 p304 p344 p345 p346 p381 p387 p668 p1078 p1082 : Prop)
    (h9382 : (¬ p227) ∨ (¬ p304) ∨ (¬ p1078))
    (h21885 : p1082 ∨ p1078)
    (h7033 : (¬ p344) ∨ (¬ p346))
    (h16655 : (¬ p227) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p668) ∨ (¬ p1082))
    (h21358 : p345 ∨ p344)
    (h22566 : p4 ∨ p344)
    (h15559 : p125 ∨ (¬ p304) ∨ (¬ p345))
    (h2079 : (¬ p125) ∨ (¬ p227) ∨ (¬ p381))
    (h20914 : p387 ∨ p381)
    (h10254 : (¬ p4) ∨ (¬ p224) ∨ (¬ p387))
    (h24673 : p224 ∨ p668) : (¬ p346) ∨ (¬ p227) ∨ (¬ p304) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p346 := by
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
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1078) := by
    rcases h9382 with q0 | q1 | q2
    · exact False.elim (q0 u1)
    · exact False.elim (q1 u2)
    · exact q2
  have u4 : p1082 := by
    rcases h21885 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u5 : (¬ p344) := by
    rcases h7033 with q0 | q1
    · exact q0
    · exact False.elim (q1 u0)
  have u6 : (¬ p668) := by
    rcases h16655 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u1)
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u0)
    · exact q3
    · exact False.elim (q4 u4)
  have u7 : p345 := by
    rcases h21358 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u8 : p4 := by
    rcases h22566 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u9 : p125 := by
    rcases h15559 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u7)
  have u10 : (¬ p381) := by
    rcases h2079 with q0 | q1 | q2
    · exact False.elim (q0 u9)
    · exact False.elim (q1 u1)
    · exact q2
  have u11 : p387 := by
    rcases h20914 with q0 | q1
    · exact q0
    · exact False.elim (u10 q1)
  have u12 : (¬ p224) := by
    rcases h10254 with q0 | q1 | q2
    · exact False.elim (q0 u8)
    · exact q1
    · exact False.elim (q2 u11)
  rcases h24673 with q0 | q1
  · exact False.elim (u12 q0)
  · exact False.elim (u6 q1)

theorem step24676 (p14 p15 p44 p48 p63 p69 p142 p167 : Prop)
    (h17360 : (¬ p14) ∨ (¬ p15) ∨ (¬ p142) ∨ (¬ p167))
    (h11337 : (¬ p14) ∨ (¬ p44) ∨ (¬ p167))
    (h21946 : p69 ∨ p15)
    (h21322 : p48 ∨ p44)
    (h11773 : (¬ p48) ∨ (¬ p63) ∨ (¬ p69)) : (¬ p167) ∨ (¬ p14) ∨ (¬ p142) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p15) := by
    rcases h17360 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u1)
    · exact q1
    · exact False.elim (q2 u2)
    · exact False.elim (q3 u0)
  have u5 : (¬ p44) := by
    rcases h11337 with q0 | q1 | q2
    · exact False.elim (q0 u1)
    · exact q1
    · exact False.elim (q2 u0)
  have u6 : p69 := by
    rcases h21946 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u7 : p48 := by
    rcases h21322 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h11773 with q0 | q1 | q2
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u6)

theorem step24678 (p326 p329 p332 p333 p334 p335 p336 p341 : Prop)
    (h1803 : p332 ∨ p341)
    (h1813 : p334 ∨ p341)
    (h1818 : p335 ∨ p341)
    (h1823 : p336 ∨ p341)
    (h1715 : p326 ∨ p329 ∨ (¬ p332) ∨ (¬ p333) ∨ (¬ p334) ∨ (¬ p335) ∨ (¬ p336)) : p341 ∨ (¬ p333) ∨ p326 ∨ p329 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p341) := fun hu => hn (Or.inl hu)
  have u1 : p333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p326) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p329) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p332 := by
    rcases h1803 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p334 := by
    rcases h1813 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p335 := by
    rcases h1818 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p336 := by
    rcases h1823 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1715 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24679 (p226 p563 p568 p569 p570 p571 p572 p573 : Prop)
    (h3232 : p568 ∨ p569)
    (h3233 : p568 ∨ p570)
    (h3234 : p568 ∨ p571)
    (h3236 : p568 ∨ p573)
    (h3151 : p226 ∨ p563 ∨ (¬ p569) ∨ (¬ p570) ∨ (¬ p571) ∨ (¬ p572) ∨ (¬ p573)) : p568 ∨ (¬ p572) ∨ p226 ∨ p563 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p568) := fun hu => hn (Or.inl hu)
  have u1 : p572 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p226) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p563) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p569 := by
    rcases h3232 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p570 := by
    rcases h3233 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p571 := by
    rcases h3234 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p573 := by
    rcases h3236 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3151 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step24680 (p226 p563 p564 p565 p566 p567 p568 p573 : Prop)
    (h3216 : p564 ∨ p573)
    (h3221 : p565 ∨ p573)
    (h3226 : p566 ∨ p573)
    (h3231 : p567 ∨ p573)
    (h3126 : p226 ∨ p563 ∨ (¬ p564) ∨ (¬ p565) ∨ (¬ p566) ∨ (¬ p567) ∨ (¬ p568)) : p573 ∨ (¬ p568) ∨ p226 ∨ p563 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p573) := fun hu => hn (Or.inl hu)
  have u1 : p568 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p226) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p563) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p564 := by
    rcases h3216 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p565 := by
    rcases h3221 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p566 := by
    rcases h3226 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p567 := by
    rcases h3231 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3126 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24681 (p226 p563 p564 p565 p566 p567 p568 p569 : Prop)
    (h3212 : p564 ∨ p569)
    (h3217 : p565 ∨ p569)
    (h3222 : p566 ∨ p569)
    (h3227 : p567 ∨ p569)
    (h3126 : p226 ∨ p563 ∨ (¬ p564) ∨ (¬ p565) ∨ (¬ p566) ∨ (¬ p567) ∨ (¬ p568)) : p569 ∨ (¬ p568) ∨ p226 ∨ p563 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p569) := fun hu => hn (Or.inl hu)
  have u1 : p568 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p226) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p563) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p564 := by
    rcases h3212 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p565 := by
    rcases h3217 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p566 := by
    rcases h3222 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p567 := by
    rcases h3227 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3126 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24682 (p226 p563 p564 p565 p566 p567 p568 p570 : Prop)
    (h3213 : p564 ∨ p570)
    (h3218 : p565 ∨ p570)
    (h3223 : p566 ∨ p570)
    (h3228 : p567 ∨ p570)
    (h3126 : p226 ∨ p563 ∨ (¬ p564) ∨ (¬ p565) ∨ (¬ p566) ∨ (¬ p567) ∨ (¬ p568)) : p570 ∨ (¬ p568) ∨ p226 ∨ p563 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p570) := fun hu => hn (Or.inl hu)
  have u1 : p568 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p226) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p563) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p564 := by
    rcases h3213 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p565 := by
    rcases h3218 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p566 := by
    rcases h3223 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p567 := by
    rcases h3228 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3126 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24683 (p226 p563 p564 p565 p566 p567 p568 p569 p570 p571 p572 p573 : Prop)
    (h24679 : p568 ∨ (¬ p572) ∨ p226 ∨ p563)
    (h24680 : p573 ∨ (¬ p568) ∨ p226 ∨ p563)
    (h24681 : p569 ∨ (¬ p568) ∨ p226 ∨ p563)
    (h24682 : p570 ∨ (¬ p568) ∨ p226 ∨ p563)
    (h3151 : p226 ∨ p563 ∨ (¬ p569) ∨ (¬ p570) ∨ (¬ p571) ∨ (¬ p572) ∨ (¬ p573))
    (h3214 : p564 ∨ p571)
    (h3219 : p565 ∨ p571)
    (h3224 : p566 ∨ p571)
    (h3229 : p567 ∨ p571)
    (h3126 : p226 ∨ p563 ∨ (¬ p564) ∨ (¬ p565) ∨ (¬ p566) ∨ (¬ p567) ∨ (¬ p568)) : (¬ p572) ∨ p563 ∨ p226 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p572 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p563) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p226) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p568 := by
    rcases h24679 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u2 q2)
    · exact False.elim (u1 q3)
  have u4 : p573 := by
    rcases h24680 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u2 q2)
    · exact False.elim (u1 q3)
  have u5 : p569 := by
    rcases h24681 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u2 q2)
    · exact False.elim (u1 q3)
  have u6 : p570 := by
    rcases h24682 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u2 q2)
    · exact False.elim (u1 q3)
  have u7 : (¬ p571) := by
    rcases h3151 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u6)
    · exact q4
    · exact False.elim (q5 u0)
    · exact False.elim (q6 u4)
  have u8 : p564 := by
    rcases h3214 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p565 := by
    rcases h3219 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p566 := by
    rcases h3224 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p567 := by
    rcases h3229 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h3126 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u3)

theorem step24684 (p226 p563 p564 p565 p566 p567 p568 p572 : Prop)
    (h24683 : (¬ p572) ∨ p563 ∨ p226)
    (h3215 : p564 ∨ p572)
    (h3220 : p565 ∨ p572)
    (h3225 : p566 ∨ p572)
    (h3230 : p567 ∨ p572)
    (h3235 : p568 ∨ p572)
    (h3126 : p226 ∨ p563 ∨ (¬ p564) ∨ (¬ p565) ∨ (¬ p566) ∨ (¬ p567) ∨ (¬ p568)) : p563 ∨ p226 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p563) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p226) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p572) := by
    rcases h24683 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p564 := by
    rcases h3215 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : p565 := by
    rcases h3220 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p566 := by
    rcases h3225 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p567 := by
    rcases h3230 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p568 := by
    rcases h3235 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h3126 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24685 (p3 p8 p163 p226 p540 p544 p557 p563 p657 p796 : Prop)
    (h19540 : (¬ p163) ∨ (¬ p544) ∨ (¬ p657) ∨ (¬ p796))
    (h21071 : p540 ∨ p544)
    (h9322 : (¬ p8) ∨ p544 ∨ (¬ p557))
    (h16972 : (¬ p8) ∨ (¬ p163) ∨ (¬ p540) ∨ (¬ p563) ∨ (¬ p796))
    (h21089 : p3 ∨ p557)
    (h9368 : (¬ p3) ∨ (¬ p226))
    (h24684 : p563 ∨ p226) : (¬ p163) ∨ (¬ p657) ∨ (¬ p8) ∨ (¬ p796) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p544) := by
    rcases h19540 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u3)
  have u5 : p540 := by
    rcases h21071 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u6 : (¬ p557) := by
    rcases h9322 with q0 | q1 | q2
    · exact False.elim (q0 u2)
    · exact False.elim (u4 q1)
    · exact q2
  have u7 : (¬ p563) := by
    rcases h16972 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u2)
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u5)
    · exact q3
    · exact False.elim (q4 u3)
  have u8 : p3 := by
    rcases h21089 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : (¬ p226) := by
    rcases h9368 with q0 | q1
    · exact False.elim (q0 u8)
    · exact q1
  rcases h24684 with q0 | q1
  · exact False.elim (u7 q0)
  · exact False.elim (u9 q1)

theorem step24689 (p50 p69 p167 p229 p879 p883 p1096 : Prop)
    (h10795 : (¬ p69) ∨ (¬ p879) ∨ (¬ p1096))
    (h16787 : (¬ p50) ∨ (¬ p69) ∨ (¬ p167) ∨ (¬ p883) ∨ (¬ p1096))
    (h23012 : p883 ∨ p879 ∨ p229) : (¬ p1096) ∨ (¬ p50) ∨ (¬ p69) ∨ p229 ∨ (¬ p167) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p50 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p879) := by
    rcases h10795 with q0 | q1 | q2
    · exact False.elim (q0 u2)
    · exact q1
    · exact False.elim (q2 u0)
  have u6 : (¬ p883) := by
    rcases h16787 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u1)
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u4)
    · exact q3
    · exact False.elim (q4 u0)
  rcases h23012 with q0 | q1 | q2
  · exact False.elim (u6 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (u3 q2)

theorem step24690 (p85 p227 p455 p456 p495 p498 p499 p582 p1206 : Prop)
    (h20942 : p495 ∨ p499)
    (h24487 : p498 ∨ p495)
    (h16776 : (¬ p85) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p1206))
    (h16832 : (¬ p85) ∨ (¬ p227) ∨ (¬ p456) ∨ (¬ p498) ∨ (¬ p582))
    (h20925 : p455 ∨ p456) : p495 ∨ (¬ p85) ∨ (¬ p227) ∨ (¬ p1206) ∨ (¬ p582) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p495) := fun hu => hn (Or.inl hu)
  have u1 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p499 := by
    rcases h20942 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p498 := by
    rcases h24487 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : (¬ p455) := by
    rcases h16776 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u1)
    · exact q1
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u3)
  have u8 : (¬ p456) := by
    rcases h16832 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u1)
    · exact False.elim (q1 u2)
    · exact q2
    · exact False.elim (q3 u6)
    · exact False.elim (q4 u4)
  rcases h20925 with q0 | q1
  · exact False.elim (u7 q0)
  · exact False.elim (u8 q1)

theorem step24691 (p3 p12 p165 p169 p195 p1115 p1116 : Prop)
    (h21858 : p1115 ∨ p1116)
    (h14625 : (¬ p12) ∨ (¬ p169) ∨ p1116)
    (h17021 : (¬ p3) ∨ (¬ p12) ∨ (¬ p165) ∨ (¬ p195) ∨ (¬ p1115))
    (h21921 : p165 ∨ p169) : p1116 ∨ (¬ p12) ∨ (¬ p195) ∨ (¬ p3) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1116) := fun hu => hn (Or.inl hu)
  have u1 : p12 := by
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
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1115 := by
    rcases h21858 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : (¬ p169) := by
    rcases h14625 with q0 | q1 | q2
    · exact False.elim (q0 u1)
    · exact q1
    · exact False.elim (u0 q2)
  have u6 : (¬ p165) := by
    rcases h17021 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u3)
    · exact False.elim (q1 u1)
    · exact q2
    · exact False.elim (q3 u2)
    · exact False.elim (q4 u4)
  rcases h21921 with q0 | q1
  · exact False.elim (u6 q0)
  · exact False.elim (u5 q1)

theorem step24692 (p227 p349 p363 p367 p434 p687 p690 p1084 : Prop)
    (h20766 : p690 ∨ p687)
    (h11942 : (¬ p367) ∨ (¬ p434) ∨ p687)
    (h17277 : (¬ p227) ∨ (¬ p349) ∨ (¬ p363) ∨ (¬ p434) ∨ (¬ p690) ∨ (¬ p1084))
    (h22481 : p363 ∨ p367) : p687 ∨ (¬ p434) ∨ (¬ p227) ∨ (¬ p1084) ∨ (¬ p349) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p687) := fun hu => hn (Or.inl hu)
  have u1 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p690 := by
    rcases h20766 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : (¬ p367) := by
    rcases h11942 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u1)
    · exact False.elim (u0 q2)
  have u7 : (¬ p363) := by
    rcases h17277 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u2)
    · exact False.elim (q1 u4)
    · exact q2
    · exact False.elim (q3 u1)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u3)
  rcases h22481 with q0 | q1
  · exact False.elim (u7 q0)
  · exact False.elim (u6 q1)

theorem step24693 (p1385 p1394 p1396 p1397 p1398 p1399 p1400 p1401 p1402 p1403 p1404 p1405 : Prop)
    (h22645 : p1400 ∨ p1394 ∨ p1385)
    (h22646 : p1405 ∨ p1394 ∨ p1385)
    (h22647 : p1404 ∨ p1394 ∨ p1385)
    (h22648 : p1403 ∨ p1394 ∨ p1385)
    (h22649 : p1402 ∨ p1394 ∨ p1385)
    (h8387 : p1385 ∨ p1394 ∨ (¬ p1401) ∨ (¬ p1402) ∨ (¬ p1403) ∨ (¬ p1404) ∨ (¬ p1405))
    (h8449 : p1396 ∨ p1401)
    (h8454 : p1397 ∨ p1401)
    (h8459 : p1398 ∨ p1401)
    (h8464 : p1399 ∨ p1401)
    (h8362 : p1385 ∨ p1394 ∨ (¬ p1396) ∨ (¬ p1397) ∨ (¬ p1398) ∨ (¬ p1399) ∨ (¬ p1400)) : p1394 ∨ p1385 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1394) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1385) := fun hu => hn (Or.inr hu)
  have u2 : p1400 := by
    rcases h22645 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1405 := by
    rcases h22646 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1404 := by
    rcases h22647 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1403 := by
    rcases h22648 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p1402 := by
    rcases h22649 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p1401) := by
    rcases h8387 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact q2
    · exact False.elim (q3 u6)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u3)
  have u8 : p1396 := by
    rcases h8449 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p1397 := by
    rcases h8454 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p1398 := by
    rcases h8459 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p1399 := by
    rcases h8464 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h8362 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u2)

theorem step24694 (p15 p70 p73 p78 p79 p80 p81 p82 : Prop)
    (h370 : p73 ∨ p79)
    (h371 : p73 ∨ p80)
    (h372 : p73 ∨ p81)
    (h373 : p73 ∨ p82)
    (h311 : p15 ∨ p70 ∨ (¬ p78) ∨ (¬ p79) ∨ (¬ p80) ∨ (¬ p81) ∨ (¬ p82)) : p73 ∨ (¬ p78) ∨ p70 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p73) := fun hu => hn (Or.inl hu)
  have u1 : p78 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p70) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p79 := by
    rcases h370 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p80 := by
    rcases h371 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p81 := by
    rcases h372 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p82 := by
    rcases h373 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h311 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24695 (p15 p70 p74 p78 p79 p80 p81 p82 : Prop)
    (h375 : p74 ∨ p79)
    (h376 : p74 ∨ p80)
    (h377 : p74 ∨ p81)
    (h378 : p74 ∨ p82)
    (h311 : p15 ∨ p70 ∨ (¬ p78) ∨ (¬ p79) ∨ (¬ p80) ∨ (¬ p81) ∨ (¬ p82)) : p74 ∨ (¬ p78) ∨ p70 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p74) := fun hu => hn (Or.inl hu)
  have u1 : p78 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p70) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p79 := by
    rcases h375 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p80 := by
    rcases h376 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p81 := by
    rcases h377 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p82 := by
    rcases h378 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h311 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24696 (p15 p70 p75 p78 p79 p80 p81 p82 : Prop)
    (h380 : p75 ∨ p79)
    (h381 : p75 ∨ p80)
    (h382 : p75 ∨ p81)
    (h383 : p75 ∨ p82)
    (h311 : p15 ∨ p70 ∨ (¬ p78) ∨ (¬ p79) ∨ (¬ p80) ∨ (¬ p81) ∨ (¬ p82)) : p75 ∨ (¬ p78) ∨ p70 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p75) := fun hu => hn (Or.inl hu)
  have u1 : p78 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p70) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p79 := by
    rcases h380 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p80 := by
    rcases h381 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p81 := by
    rcases h382 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p82 := by
    rcases h383 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h311 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24697 (p15 p70 p76 p78 p79 p80 p81 p82 : Prop)
    (h385 : p76 ∨ p79)
    (h386 : p76 ∨ p80)
    (h387 : p76 ∨ p81)
    (h388 : p76 ∨ p82)
    (h311 : p15 ∨ p70 ∨ (¬ p78) ∨ (¬ p79) ∨ (¬ p80) ∨ (¬ p81) ∨ (¬ p82)) : p76 ∨ (¬ p78) ∨ p70 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p76) := fun hu => hn (Or.inl hu)
  have u1 : p78 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p70) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p79 := by
    rcases h385 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p80 := by
    rcases h386 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p81 := by
    rcases h387 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p82 := by
    rcases h388 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h311 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24698 (p15 p70 p73 p74 p75 p76 p77 p78 p79 p80 p81 p82 : Prop)
    (h24694 : p73 ∨ (¬ p78) ∨ p70 ∨ p15)
    (h24695 : p74 ∨ (¬ p78) ∨ p70 ∨ p15)
    (h24696 : p75 ∨ (¬ p78) ∨ p70 ∨ p15)
    (h24697 : p76 ∨ (¬ p78) ∨ p70 ∨ p15)
    (h286 : p15 ∨ p70 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77))
    (h390 : p77 ∨ p79)
    (h391 : p77 ∨ p80)
    (h392 : p77 ∨ p81)
    (h393 : p77 ∨ p82)
    (h311 : p15 ∨ p70 ∨ (¬ p78) ∨ (¬ p79) ∨ (¬ p80) ∨ (¬ p81) ∨ (¬ p82)) : (¬ p78) ∨ p70 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p78 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p70) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p73 := by
    rcases h24694 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u4 : p74 := by
    rcases h24695 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u5 : p75 := by
    rcases h24696 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u6 : p76 := by
    rcases h24697 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u7 : (¬ p77) := by
    rcases h286 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p79 := by
    rcases h390 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p80 := by
    rcases h391 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p81 := by
    rcases h392 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p82 := by
    rcases h393 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h311 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step24699 (p15 p70 p73 p74 p75 p76 p77 p78 : Prop)
    (h24698 : (¬ p78) ∨ p70 ∨ p15)
    (h369 : p73 ∨ p78)
    (h374 : p74 ∨ p78)
    (h379 : p75 ∨ p78)
    (h384 : p76 ∨ p78)
    (h389 : p77 ∨ p78)
    (h286 : p15 ∨ p70 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77)) : p70 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p70) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p78) := by
    rcases h24698 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p73 := by
    rcases h369 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : p74 := by
    rcases h374 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p75 := by
    rcases h379 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p76 := by
    rcases h384 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p77 := by
    rcases h389 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h286 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24700 (p3 p69 p229 p346 p544 p595 p664 p879 p883 p1076 p1077 p1096 p1099 : Prop)
    (h17896 : (¬ p3) ∨ (¬ p346) ∨ (¬ p544) ∨ (¬ p1077))
    (h21482 : p1077 ∨ p1076)
    (h23302 : (¬ p595) ∨ (¬ p1099) ∨ (¬ p664) ∨ (¬ p1076) ∨ (¬ p346))
    (h21802 : p1096 ∨ p1099)
    (h10795 : (¬ p69) ∨ (¬ p879) ∨ (¬ p1096))
    (h19319 : (¬ p69) ∨ (¬ p346) ∨ (¬ p544) ∨ (¬ p883) ∨ (¬ p1096))
    (h23012 : p883 ∨ p879 ∨ p229) : (¬ p346) ∨ (¬ p595) ∨ (¬ p664) ∨ (¬ p544) ∨ p229 ∨ (¬ p3) ∨ (¬ p69) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p1077) := by
    rcases h17896 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u5)
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u3)
    · exact q3
  have u8 : p1076 := by
    rcases h21482 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : (¬ p1099) := by
    rcases h23302 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u1)
    · exact q1
    · exact False.elim (q2 u2)
    · exact False.elim (q3 u8)
    · exact False.elim (q4 u0)
  have u10 : p1096 := by
    rcases h21802 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  have u11 : (¬ p879) := by
    rcases h10795 with q0 | q1 | q2
    · exact False.elim (q0 u6)
    · exact q1
    · exact False.elim (q2 u10)
  have u12 : (¬ p883) := by
    rcases h19319 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u6)
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u3)
    · exact q3
    · exact False.elim (q4 u10)
  rcases h23012 with q0 | q1 | q2
  · exact False.elim (u12 q0)
  · exact False.elim (u11 q1)
  · exact False.elim (u4 q2)

theorem step24701 (p10 p18 p19 p27 p101 p102 p323 p344 p387 p495 p595 p596 p633 p657 : Prop)
    (h22840 : p19 ∨ p18)
    (h24295 : p27 ∨ p18)
    (h17986 : (¬ p19) ∨ (¬ p102) ∨ (¬ p344) ∨ (¬ p657))
    (h17894 : (¬ p10) ∨ (¬ p27) ∨ (¬ p495) ∨ (¬ p595) ∨ (¬ p596))
    (h21623 : p101 ∨ p102)
    (h21681 : p323 ∨ p10)
    (h17788 : (¬ p101) ∨ (¬ p323) ∨ (¬ p387) ∨ (¬ p633)) : p18 ∨ (¬ p633) ∨ (¬ p596) ∨ (¬ p495) ∨ (¬ p344) ∨ (¬ p387) ∨ (¬ p595) ∨ (¬ p657) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p18) := fun hu => hn (Or.inl hu)
  have u1 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p596 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p19 := by
    rcases h22840 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p27 := by
    rcases h24295 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : (¬ p102) := by
    rcases h17986 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u8)
    · exact q1
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u7)
  have u11 : (¬ p10) := by
    rcases h17894 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u9)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u6)
    · exact False.elim (q4 u2)
  have u12 : p101 := by
    rcases h21623 with q0 | q1
    · exact q0
    · exact False.elim (u10 q1)
  have u13 : p323 := by
    rcases h21681 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  rcases h17788 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u12)
  · exact False.elim (q1 u13)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)

theorem step24702 (p18 p27 p69 p344 p348 p351 p386 p387 p420 p456 p461 p495 p594 p595 p596 p599 p601 p616 p633 p636 p657 p902 p1084 p1206 p1213 p1229 p1232 : Prop)
    (h21790 : p616 ∨ p595)
    (h12881 : (¬ p495) ∨ (¬ p594) ∨ p616)
    (h22291 : p596 ∨ p594)
    (h22899 : p594 ∨ p601)
    (h5067 : (¬ p420) ∨ (¬ p601))
    (h12101 : (¬ p386) ∨ p420 ∨ (¬ p456))
    (h24566 : p461 ∨ p456)
    (h13340 : (¬ p348) ∨ (¬ p596) ∨ p902)
    (h14505 : (¬ p351) ∨ p599 ∨ (¬ p902))
    (h22609 : (¬ p1232) ∨ p616 ∨ (¬ p599) ∨ (¬ p387))
    (h22374 : p1229 ∨ p1232)
    (h16594 : (¬ p461) ∨ (¬ p495) ∨ (¬ p636) ∨ (¬ p1084) ∨ (¬ p1229))
    (h21879 : p636 ∨ p633)
    (h24701 : p18 ∨ (¬ p633) ∨ (¬ p596) ∨ (¬ p495) ∨ (¬ p344) ∨ (¬ p387) ∨ (¬ p595) ∨ (¬ p657))
    (h17631 : (¬ p18) ∨ p27)
    (h24312 : (¬ p69) ∨ (¬ p18) ∨ (¬ p1213) ∨ (¬ p1229))
    (h16676 : (¬ p27) ∨ (¬ p461) ∨ (¬ p495) ∨ (¬ p1206) ∨ (¬ p1229))
    (h24268 : p1213 ∨ p1206) : (¬ p495) ∨ (¬ p1084) ∨ (¬ p351) ∨ (¬ p348) ∨ (¬ p344) ∨ (¬ p386) ∨ (¬ p387) ∨ p616 ∨ (¬ p657) ∨ (¬ p69) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p386 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p616) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p595 := by
    rcases h21790 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : (¬ p594) := by
    rcases h12881 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (u7 q2)
  have u12 : p596 := by
    rcases h22291 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  have u13 : p601 := by
    rcases h22899 with q0 | q1
    · exact False.elim (u11 q0)
    · exact q1
  have u14 : (¬ p420) := by
    rcases h5067 with q0 | q1
    · exact q0
    · exact False.elim (q1 u13)
  have u15 : (¬ p456) := by
    rcases h12101 with q0 | q1 | q2
    · exact False.elim (q0 u5)
    · exact False.elim (u14 q1)
    · exact q2
  have u16 : p461 := by
    rcases h24566 with q0 | q1
    · exact q0
    · exact False.elim (u15 q1)
  have u17 : p902 := by
    rcases h13340 with q0 | q1 | q2
    · exact False.elim (q0 u3)
    · exact False.elim (q1 u12)
    · exact q2
  have u18 : p599 := by
    rcases h14505 with q0 | q1 | q2
    · exact False.elim (q0 u2)
    · exact q1
    · exact False.elim (q2 u17)
  have u19 : (¬ p1232) := by
    rcases h22609 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (u7 q1)
    · exact False.elim (q2 u18)
    · exact False.elim (q3 u6)
  have u20 : p1229 := by
    rcases h22374 with q0 | q1
    · exact q0
    · exact False.elim (u19 q1)
  have u21 : (¬ p636) := by
    rcases h16594 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u16)
    · exact False.elim (q1 u0)
    · exact q2
    · exact False.elim (q3 u1)
    · exact False.elim (q4 u20)
  have u22 : p633 := by
    rcases h21879 with q0 | q1
    · exact False.elim (u21 q0)
    · exact q1
  have u23 : p18 := by
    rcases h24701 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
    · exact q0
    · exact False.elim (q1 u22)
    · exact False.elim (q2 u12)
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u6)
    · exact False.elim (q6 u10)
    · exact False.elim (q7 u8)
  have u24 : p27 := by
    rcases h17631 with q0 | q1
    · exact False.elim (q0 u23)
    · exact q1
  have u25 : (¬ p1213) := by
    rcases h24312 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u9)
    · exact False.elim (q1 u23)
    · exact q2
    · exact False.elim (q3 u20)
  have u26 : (¬ p1206) := by
    rcases h16676 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u24)
    · exact False.elim (q1 u16)
    · exact False.elim (q2 u0)
    · exact q3
    · exact False.elim (q4 u20)
  rcases h24268 with q0 | q1
  · exact False.elim (u25 q0)
  · exact False.elim (u26 q1)

theorem step24703 (p45 p63 p69 p85 p595 p616 p802 p1385 p1387 p1391 p1393 : Prop)
    (h24634 : p802)
    (h21790 : p616 ∨ p595)
    (h22350 : p1385 ∨ p1393)
    (h24635 : (¬ p69) ∨ (¬ p1393) ∨ (¬ p63))
    (h22211 : p85 ∨ p63)
    (h11318 : (¬ p85) ∨ p616 ∨ (¬ p1387))
    (h16774 : (¬ p45) ∨ (¬ p85) ∨ (¬ p595) ∨ (¬ p802) ∨ (¬ p1391))
    (h22523 : p1391 ∨ p1387 ∨ p1385) : p1385 ∨ (¬ p45) ∨ (¬ p69) ∨ p616 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1385) := fun hu => hn (Or.inl hu)
  have u1 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p616) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p802 := by
    exact h24634
  have u5 : p595 := by
    rcases h21790 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  have u6 : p1393 := by
    rcases h22350 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : (¬ p63) := by
    rcases h24635 with q0 | q1 | q2
    · exact False.elim (q0 u2)
    · exact False.elim (q1 u6)
    · exact q2
  have u8 : p85 := by
    rcases h22211 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : (¬ p1387) := by
    rcases h11318 with q0 | q1 | q2
    · exact False.elim (q0 u8)
    · exact False.elim (u3 q1)
    · exact q2
  have u10 : (¬ p1391) := by
    rcases h16774 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u1)
    · exact False.elim (q1 u8)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u4)
    · exact q4
  rcases h22523 with q0 | q1 | q2
  · exact False.elim (u10 q0)
  · exact False.elim (u9 q1)
  · exact False.elim (u0 q2)

theorem step24704 (p39 p41 p48 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 : Prop)
    (h23950 : p51 ∨ p39 ∨ p41)
    (h23951 : p55 ∨ p39 ∨ p41)
    (h23952 : p54 ∨ p39 ∨ p41)
    (h23953 : p53 ∨ p39 ∨ p41)
    (h149 : p39 ∨ p48 ∨ (¬ p51) ∨ (¬ p52) ∨ (¬ p53) ∨ (¬ p54) ∨ (¬ p55))
    (h238 : p52 ∨ p56)
    (h239 : p52 ∨ p57)
    (h240 : p52 ∨ p58)
    (h241 : p52 ∨ p59)
    (h242 : p52 ∨ p60)
    (h175 : p39 ∨ p41 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60)) : p39 ∨ p48 ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p39) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p48) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p51 := by
    rcases h23950 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u4 : p55 := by
    rcases h23951 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u5 : p54 := by
    rcases h23952 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u6 : p53 := by
    rcases h23953 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u7 : (¬ p52) := by
    rcases h149 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u0 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u3)
    · exact q3
    · exact False.elim (q4 u6)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u4)
  have u8 : p56 := by
    rcases h238 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p57 := by
    rcases h239 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p58 := by
    rcases h240 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p59 := by
    rcases h241 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u12 : p60 := by
    rcases h242 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h175 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u12)

theorem step24705 (p39 p69 p84 p89 p790 p1385 : Prop)
    (h11493 : (¬ p84) ∨ (¬ p790) ∨ (¬ p1385))
    (h17416 : (¬ p39) ∨ (¬ p69) ∨ (¬ p89) ∨ (¬ p790) ∨ (¬ p1385))
    (h22277 : p89 ∨ p84) : (¬ p790) ∨ (¬ p39) ∨ (¬ p1385) ∨ (¬ p69) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p84) := by
    rcases h11493 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u2)
  have u5 : (¬ p89) := by
    rcases h17416 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u1)
    · exact False.elim (q1 u3)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u2)
  rcases h22277 with q0 | q1
  · exact False.elim (u5 q0)
  · exact False.elim (u4 q1)

theorem step24706 (p41 p44 p45 p63 p69 p134 p135 p136 p576 p581 : Prop)
    (h23818 : p41 ∨ p44)
    (h21444 : p41 ∨ p45)
    (h12204 : (¬ p576) ∨ (¬ p581))
    (h17202 : (¬ p44) ∨ (¬ p63) ∨ (¬ p69) ∨ (¬ p135) ∨ (¬ p581))
    (h11334 : (¬ p45) ∨ (¬ p136) ∨ p576)
    (h24376 : p134 ∨ p136 ∨ p135) : (¬ p581) ∨ p134 ∨ (¬ p63) ∨ p41 ∨ (¬ p69) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p134) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p44 := by
    rcases h23818 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  have u6 : p45 := by
    rcases h21444 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  have u7 : (¬ p576) := by
    rcases h12204 with q0 | q1
    · exact q0
    · exact False.elim (q1 u0)
  have u8 : (¬ p135) := by
    rcases h17202 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u5)
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u4)
    · exact q3
    · exact False.elim (q4 u0)
  have u9 : (¬ p136) := by
    rcases h11334 with q0 | q1 | q2
    · exact False.elim (q0 u6)
    · exact q1
    · exact False.elim (u7 q2)
  rcases h24376 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u9 q1)
  · exact False.elim (u8 q2)

theorem step24708 (p20 p26 p28 p29 p30 p31 p32 p37 : Prop)
    (h109 : p28 ∨ p37)
    (h114 : p29 ∨ p37)
    (h119 : p30 ∨ p37)
    (h124 : p31 ∨ p37)
    (h129 : p32 ∨ p37)
    (h8 : p20 ∨ p26 ∨ (¬ p28) ∨ (¬ p29) ∨ (¬ p30) ∨ (¬ p31) ∨ (¬ p32)) : p37 ∨ p26 ∨ p20 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p37) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p26) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p20) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p28 := by
    rcases h109 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p29 := by
    rcases h114 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p30 := by
    rcases h119 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p31 := by
    rcases h124 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p32 := by
    rcases h129 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24709 (p18 p26 p28 p33 p34 p35 p36 p37 : Prop)
    (h105 : p28 ∨ p33)
    (h106 : p28 ∨ p34)
    (h107 : p28 ∨ p35)
    (h108 : p28 ∨ p36)
    (h43 : p18 ∨ p26 ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p36) ∨ (¬ p37)) : p28 ∨ (¬ p37) ∨ p26 ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p28) := fun hu => hn (Or.inl hu)
  have u1 : p37 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p26) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p33 := by
    rcases h105 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p34 := by
    rcases h106 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p35 := by
    rcases h107 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p36 := by
    rcases h108 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h43 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24710 (p18 p26 p29 p33 p34 p35 p36 p37 : Prop)
    (h110 : p29 ∨ p33)
    (h111 : p29 ∨ p34)
    (h112 : p29 ∨ p35)
    (h113 : p29 ∨ p36)
    (h43 : p18 ∨ p26 ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p36) ∨ (¬ p37)) : p29 ∨ (¬ p37) ∨ p26 ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p29) := fun hu => hn (Or.inl hu)
  have u1 : p37 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p26) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p33 := by
    rcases h110 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p34 := by
    rcases h111 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p35 := by
    rcases h112 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p36 := by
    rcases h113 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h43 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24711 (p18 p26 p30 p33 p34 p35 p36 p37 : Prop)
    (h115 : p30 ∨ p33)
    (h116 : p30 ∨ p34)
    (h117 : p30 ∨ p35)
    (h118 : p30 ∨ p36)
    (h43 : p18 ∨ p26 ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p36) ∨ (¬ p37)) : p30 ∨ (¬ p37) ∨ p26 ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p30) := fun hu => hn (Or.inl hu)
  have u1 : p37 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p26) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p33 := by
    rcases h115 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p34 := by
    rcases h116 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p35 := by
    rcases h117 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p36 := by
    rcases h118 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h43 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24712 (p18 p26 p31 p33 p34 p35 p36 p37 : Prop)
    (h120 : p31 ∨ p33)
    (h121 : p31 ∨ p34)
    (h122 : p31 ∨ p35)
    (h123 : p31 ∨ p36)
    (h43 : p18 ∨ p26 ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p36) ∨ (¬ p37)) : p31 ∨ (¬ p37) ∨ p26 ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p31) := fun hu => hn (Or.inl hu)
  have u1 : p37 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p26) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p33 := by
    rcases h120 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p34 := by
    rcases h121 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p35 := by
    rcases h122 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p36 := by
    rcases h123 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h43 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24713 (p3 p11 p12 p13 p15 p18 p19 p20 p24 p26 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p68 p69 p102 p104 p124 p125 p126 p304 p425 p495 p499 p633 p1076 : Prop)
    (h19796 : (¬ p11) ∨ (¬ p124) ∨ (¬ p125) ∨ (¬ p126))
    (h21106 : p124 ∨ p304)
    (h6604 : (¬ p15) ∨ (¬ p69))
    (h21595 : p68 ∨ p15)
    (h9344 : (¬ p495) ∨ (¬ p499))
    (h11153 : (¬ p20) ∨ (¬ p69) ∨ (¬ p499))
    (h23663 : p425 ∨ p495)
    (h23042 : p20 ∨ p19)
    (h11188 : (¬ p304) ∨ (¬ p425) ∨ (¬ p633))
    (h4 : (¬ p18) ∨ (¬ p19))
    (h24078 : p24 ∨ p18)
    (h11161 : (¬ p24) ∨ (¬ p102) ∨ p633)
    (h21934 : p104 ∨ p102)
    (h7021 : (¬ p12) ∨ (¬ p104) ∨ (¬ p1076))
    (h22593 : p1076 ∨ p13)
    (h19152 : (¬ p3) ∨ (¬ p11) ∨ (¬ p12) ∨ (¬ p13) ∨ (¬ p26) ∨ (¬ p68) ∨ (¬ p125) ∨ (¬ p126) ∨ (¬ p425))
    (h24708 : p37 ∨ p26 ∨ p20)
    (h24709 : p28 ∨ (¬ p37) ∨ p26 ∨ p18)
    (h24710 : p29 ∨ (¬ p37) ∨ p26 ∨ p18)
    (h24711 : p30 ∨ (¬ p37) ∨ p26 ∨ p18)
    (h24712 : p31 ∨ (¬ p37) ∨ p26 ∨ p18)
    (h8 : p20 ∨ p26 ∨ (¬ p28) ∨ (¬ p29) ∨ (¬ p30) ∨ (¬ p31) ∨ (¬ p32))
    (h125 : p32 ∨ p33)
    (h126 : p32 ∨ p34)
    (h127 : p32 ∨ p35)
    (h128 : p32 ∨ p36)
    (h43 : p18 ∨ p26 ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p36) ∨ (¬ p37)) : (¬ p499) ∨ (¬ p12) ∨ (¬ p11) ∨ (¬ p126) ∨ (¬ p125) ∨ (¬ p3) ∨ (¬ p69) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p124) := by
    rcases h19796 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u2)
    · exact q1
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u3)
  have u8 : p304 := by
    rcases h21106 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : (¬ p15) := by
    rcases h6604 with q0 | q1
    · exact q0
    · exact False.elim (q1 u6)
  have u10 : p68 := by
    rcases h21595 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  have u11 : (¬ p495) := by
    rcases h9344 with q0 | q1
    · exact q0
    · exact False.elim (q1 u0)
  have u12 : (¬ p20) := by
    rcases h11153 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u6)
    · exact False.elim (q2 u0)
  have u13 : p425 := by
    rcases h23663 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  have u14 : p19 := by
    rcases h23042 with q0 | q1
    · exact False.elim (u12 q0)
    · exact q1
  have u15 : (¬ p633) := by
    rcases h11188 with q0 | q1 | q2
    · exact False.elim (q0 u8)
    · exact False.elim (q1 u13)
    · exact q2
  have u16 : (¬ p18) := by
    rcases h4 with q0 | q1
    · exact q0
    · exact False.elim (q1 u14)
  have u17 : p24 := by
    rcases h24078 with q0 | q1
    · exact q0
    · exact False.elim (u16 q1)
  have u18 : (¬ p102) := by
    rcases h11161 with q0 | q1 | q2
    · exact False.elim (q0 u17)
    · exact q1
    · exact False.elim (u15 q2)
  have u19 : p104 := by
    rcases h21934 with q0 | q1
    · exact q0
    · exact False.elim (u18 q1)
  have u20 : (¬ p1076) := by
    rcases h7021 with q0 | q1 | q2
    · exact False.elim (q0 u1)
    · exact False.elim (q1 u19)
    · exact q2
  have u21 : p13 := by
    rcases h22593 with q0 | q1
    · exact False.elim (u20 q0)
    · exact q1
  have u22 : (¬ p26) := by
    rcases h19152 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
    · exact False.elim (q0 u5)
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u21)
    · exact q4
    · exact False.elim (q5 u10)
    · exact False.elim (q6 u4)
    · exact False.elim (q7 u3)
    · exact False.elim (q8 u13)
  have u23 : p37 := by
    rcases h24708 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u22 q1)
    · exact False.elim (u12 q2)
  have u24 : p28 := by
    rcases h24709 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u23)
    · exact False.elim (u22 q2)
    · exact False.elim (u16 q3)
  have u25 : p29 := by
    rcases h24710 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u23)
    · exact False.elim (u22 q2)
    · exact False.elim (u16 q3)
  have u26 : p30 := by
    rcases h24711 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u23)
    · exact False.elim (u22 q2)
    · exact False.elim (u16 q3)
  have u27 : p31 := by
    rcases h24712 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u23)
    · exact False.elim (u22 q2)
    · exact False.elim (u16 q3)
  have u28 : (¬ p32) := by
    rcases h8 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u12 q0)
    · exact False.elim (u22 q1)
    · exact False.elim (q2 u24)
    · exact False.elim (q3 u25)
    · exact False.elim (q4 u26)
    · exact False.elim (q5 u27)
    · exact q6
  have u29 : p33 := by
    rcases h125 with q0 | q1
    · exact False.elim (u28 q0)
    · exact q1
  have u30 : p34 := by
    rcases h126 with q0 | q1
    · exact False.elim (u28 q0)
    · exact q1
  have u31 : p35 := by
    rcases h127 with q0 | q1
    · exact False.elim (u28 q0)
    · exact q1
  have u32 : p36 := by
    rcases h128 with q0 | q1
    · exact False.elim (u28 q0)
    · exact q1
  rcases h43 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u16 q0)
  · exact False.elim (u22 q1)
  · exact False.elim (q2 u29)
  · exact False.elim (q3 u30)
  · exact False.elim (q4 u31)
  · exact False.elim (q5 u32)
  · exact False.elim (q6 u23)

theorem step24714 (p18 p19 p20 p26 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 : Prop)
    (h23042 : p20 ∨ p19)
    (h24708 : p37 ∨ p26 ∨ p20)
    (h4 : (¬ p18) ∨ (¬ p19))
    (h24709 : p28 ∨ (¬ p37) ∨ p26 ∨ p18)
    (h24710 : p29 ∨ (¬ p37) ∨ p26 ∨ p18)
    (h24711 : p30 ∨ (¬ p37) ∨ p26 ∨ p18)
    (h24712 : p31 ∨ (¬ p37) ∨ p26 ∨ p18)
    (h8 : p20 ∨ p26 ∨ (¬ p28) ∨ (¬ p29) ∨ (¬ p30) ∨ (¬ p31) ∨ (¬ p32))
    (h125 : p32 ∨ p33)
    (h126 : p32 ∨ p34)
    (h127 : p32 ∨ p35)
    (h128 : p32 ∨ p36)
    (h43 : p18 ∨ p26 ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p36) ∨ (¬ p37)) : p20 ∨ p26 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p20) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p26) := fun hu => hn (Or.inr hu)
  have u2 : p19 := by
    rcases h23042 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : p37 := by
    rcases h24708 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u4 : (¬ p18) := by
    rcases h4 with q0 | q1
    · exact q0
    · exact False.elim (q1 u2)
  have u5 : p28 := by
    rcases h24709 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u4 q3)
  have u6 : p29 := by
    rcases h24710 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u4 q3)
  have u7 : p30 := by
    rcases h24711 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u4 q3)
  have u8 : p31 := by
    rcases h24712 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u4 q3)
  have u9 : (¬ p32) := by
    rcases h8 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u0 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u6)
    · exact False.elim (q4 u7)
    · exact False.elim (q5 u8)
    · exact q6
  have u10 : p33 := by
    rcases h125 with q0 | q1
    · exact False.elim (u9 q0)
    · exact q1
  have u11 : p34 := by
    rcases h126 with q0 | q1
    · exact False.elim (u9 q0)
    · exact q1
  have u12 : p35 := by
    rcases h127 with q0 | q1
    · exact False.elim (u9 q0)
    · exact q1
  have u13 : p36 := by
    rcases h128 with q0 | q1
    · exact False.elim (u9 q0)
    · exact q1
  rcases h43 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u12)
  · exact False.elim (q5 u13)
  · exact False.elim (q6 u3)

theorem step24718 (p301 p519 p522 p523 p524 p525 p526 p531 : Prop)
    (h2870 : p301 ∨ p519 ∨ (¬ p522) ∨ (¬ p523) ∨ (¬ p524) ∨ (¬ p525) ∨ (¬ p526))
    (h2963 : p522 ∨ p531)
    (h21664 : p522 ∨ (¬ p531) ∨ p519 ∨ p301) : (¬ p526) ∨ p519 ∨ p301 ∨ (¬ p523) ∨ (¬ p525) ∨ (¬ p524) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p526 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p519) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p301) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p523 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p525 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p524 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p522) := by
    rcases h2870 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact q2
    · exact False.elim (q3 u3)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u0)
  have u7 : p531 := by
    rcases h2963 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h21664 with q0 | q1 | q2 | q3
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u7)
  · exact False.elim (u1 q2)
  · exact False.elim (u2 q3)

theorem step24721 (p17 p63 p87 p125 p126 p256 p261 p265 p420 p425 p494 p577 p581 p601 : Prop)
    (h14511 : (¬ p125) ∨ p420 ∨ (¬ p425))
    (h22344 : p425 ∨ p494)
    (h21406 : p420 ∨ p601)
    (h13074 : (¬ p125) ∨ (¬ p126) ∨ (¬ p265))
    (h21151 : p17 ∨ p265)
    (h10652 : (¬ p17) ∨ (¬ p256))
    (h22105 : p261 ∨ p256)
    (h21021 : (¬ p63) ∨ p87)
    (h18110 : (¬ p63) ∨ (¬ p125) ∨ (¬ p494) ∨ (¬ p577) ∨ (¬ p601))
    (h17664 : (¬ p87) ∨ (¬ p125) ∨ (¬ p126) ∨ (¬ p261) ∨ (¬ p581))
    (h23688 : p577 ∨ p581) : (¬ p63) ∨ p420 ∨ (¬ p125) ∨ (¬ p126) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p420) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p425) := by
    rcases h14511 with q0 | q1 | q2
    · exact False.elim (q0 u2)
    · exact False.elim (u1 q1)
    · exact q2
  have u5 : p494 := by
    rcases h22344 with q0 | q1
    · exact False.elim (u4 q0)
    · exact q1
  have u6 : p601 := by
    rcases h21406 with q0 | q1
    · exact False.elim (u1 q0)
    · exact q1
  have u7 : (¬ p265) := by
    rcases h13074 with q0 | q1 | q2
    · exact False.elim (q0 u2)
    · exact False.elim (q1 u3)
    · exact q2
  have u8 : p17 := by
    rcases h21151 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : (¬ p256) := by
    rcases h10652 with q0 | q1
    · exact False.elim (q0 u8)
    · exact q1
  have u10 : p261 := by
    rcases h22105 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  have u11 : p87 := by
    rcases h21021 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u12 : (¬ p577) := by
    rcases h18110 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u0)
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u5)
    · exact q3
    · exact False.elim (q4 u6)
  have u13 : (¬ p581) := by
    rcases h17664 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u11)
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u10)
    · exact q4
  rcases h23688 with q0 | q1
  · exact False.elim (u12 q0)
  · exact False.elim (u13 q1)

theorem step24724 (p106 p107 p111 p112 p113 p114 p115 p120 : Prop)
    (h624 : p111 ∨ p120)
    (h629 : p112 ∨ p120)
    (h634 : p113 ∨ p120)
    (h639 : p114 ∨ p120)
    (h644 : p115 ∨ p120)
    (h540 : p106 ∨ p107 ∨ (¬ p111) ∨ (¬ p112) ∨ (¬ p113) ∨ (¬ p114) ∨ (¬ p115)) : p120 ∨ p106 ∨ p107 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p120) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p106) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p107) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p111 := by
    rcases h624 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p112 := by
    rcases h629 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p113 := by
    rcases h634 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p114 := by
    rcases h639 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p115 := by
    rcases h644 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h540 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24725 (p102 p106 p115 p116 p117 p118 p119 p120 : Prop)
    (h640 : p115 ∨ p116)
    (h641 : p115 ∨ p117)
    (h642 : p115 ∨ p118)
    (h643 : p115 ∨ p119)
    (h567 : p102 ∨ p106 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p115 ∨ (¬ p120) ∨ p106 ∨ p102 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p115) := fun hu => hn (Or.inl hu)
  have u1 : p120 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p106) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p102) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p116 := by
    rcases h640 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p117 := by
    rcases h641 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p118 := by
    rcases h642 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p119 := by
    rcases h643 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h567 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24726 (p102 p106 p111 p116 p117 p118 p119 p120 : Prop)
    (h620 : p111 ∨ p116)
    (h621 : p111 ∨ p117)
    (h622 : p111 ∨ p118)
    (h623 : p111 ∨ p119)
    (h567 : p102 ∨ p106 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p111 ∨ (¬ p120) ∨ p106 ∨ p102 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p111) := fun hu => hn (Or.inl hu)
  have u1 : p120 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p106) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p102) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p116 := by
    rcases h620 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p117 := by
    rcases h621 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p118 := by
    rcases h622 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p119 := by
    rcases h623 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h567 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24727 (p102 p106 p112 p116 p117 p118 p119 p120 : Prop)
    (h625 : p112 ∨ p116)
    (h626 : p112 ∨ p117)
    (h627 : p112 ∨ p118)
    (h628 : p112 ∨ p119)
    (h567 : p102 ∨ p106 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p112 ∨ (¬ p120) ∨ p106 ∨ p102 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p112) := fun hu => hn (Or.inl hu)
  have u1 : p120 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p106) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p102) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p116 := by
    rcases h625 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p117 := by
    rcases h626 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p118 := by
    rcases h627 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p119 := by
    rcases h628 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h567 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24728 (p102 p106 p113 p116 p117 p118 p119 p120 : Prop)
    (h630 : p113 ∨ p116)
    (h631 : p113 ∨ p117)
    (h632 : p113 ∨ p118)
    (h633 : p113 ∨ p119)
    (h567 : p102 ∨ p106 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p113 ∨ (¬ p120) ∨ p106 ∨ p102 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p113) := fun hu => hn (Or.inl hu)
  have u1 : p120 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p106) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p102) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p116 := by
    rcases h630 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p117 := by
    rcases h631 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p118 := by
    rcases h632 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p119 := by
    rcases h633 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h567 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24729 (p102 p106 p107 p111 p112 p113 p114 p115 p116 p117 p118 p119 p120 : Prop)
    (h24724 : p120 ∨ p106 ∨ p107)
    (h24725 : p115 ∨ (¬ p120) ∨ p106 ∨ p102)
    (h24726 : p111 ∨ (¬ p120) ∨ p106 ∨ p102)
    (h24727 : p112 ∨ (¬ p120) ∨ p106 ∨ p102)
    (h24728 : p113 ∨ (¬ p120) ∨ p106 ∨ p102)
    (h540 : p106 ∨ p107 ∨ (¬ p111) ∨ (¬ p112) ∨ (¬ p113) ∨ (¬ p114) ∨ (¬ p115))
    (h635 : p114 ∨ p116)
    (h636 : p114 ∨ p117)
    (h637 : p114 ∨ p118)
    (h638 : p114 ∨ p119)
    (h567 : p102 ∨ p106 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p106 ∨ p107 ∨ p102 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p106) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p107) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p102) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p120 := by
    rcases h24724 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p115 := by
    rcases h24725 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u0 q2)
    · exact False.elim (u2 q3)
  have u5 : p111 := by
    rcases h24726 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u0 q2)
    · exact False.elim (u2 q3)
  have u6 : p112 := by
    rcases h24727 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u0 q2)
    · exact False.elim (u2 q3)
  have u7 : p113 := by
    rcases h24728 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u0 q2)
    · exact False.elim (u2 q3)
  have u8 : (¬ p114) := by
    rcases h540 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u0 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u6)
    · exact False.elim (q4 u7)
    · exact q5
    · exact False.elim (q6 u4)
  have u9 : p116 := by
    rcases h635 with q0 | q1
    · exact False.elim (u8 q0)
    · exact q1
  have u10 : p117 := by
    rcases h636 with q0 | q1
    · exact False.elim (u8 q0)
    · exact q1
  have u11 : p118 := by
    rcases h637 with q0 | q1
    · exact False.elim (u8 q0)
    · exact q1
  have u12 : p119 := by
    rcases h638 with q0 | q1
    · exact False.elim (u8 q0)
    · exact q1
  rcases h567 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u12)
  · exact False.elim (q6 u3)

theorem step24730 (p125 p264 p301 p303 p515 p519 p523 p524 p525 p526 p789 p858 : Prop)
    (h22497 : p858 ∨ p789)
    (h13579 : (¬ p303) ∨ (¬ p515) ∨ p858)
    (h19150 : (¬ p125) ∨ (¬ p264) ∨ (¬ p303) ∨ (¬ p519) ∨ (¬ p789))
    (h22219 : p526 ∨ p515 ∨ p519)
    (h22222 : p523 ∨ p515 ∨ p519)
    (h22221 : p524 ∨ p515 ∨ p519)
    (h24718 : (¬ p526) ∨ p519 ∨ p301 ∨ (¬ p523) ∨ (¬ p525) ∨ (¬ p524))
    (h22220 : p525 ∨ p515 ∨ p519) : p858 ∨ (¬ p303) ∨ (¬ p264) ∨ (¬ p125) ∨ p301 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p858) := fun hu => hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p264 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p301) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p789 := by
    rcases h22497 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : (¬ p515) := by
    rcases h13579 with q0 | q1 | q2
    · exact False.elim (q0 u1)
    · exact q1
    · exact False.elim (u0 q2)
  have u7 : (¬ p519) := by
    rcases h19150 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u3)
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u1)
    · exact q3
    · exact False.elim (q4 u5)
  have u8 : p526 := by
    rcases h22219 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u6 q1)
    · exact False.elim (u7 q2)
  have u9 : p523 := by
    rcases h22222 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u6 q1)
    · exact False.elim (u7 q2)
  have u10 : p524 := by
    rcases h22221 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u6 q1)
    · exact False.elim (u7 q2)
  have u11 : (¬ p525) := by
    rcases h24718 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u8)
    · exact False.elim (u7 q1)
    · exact False.elim (u4 q2)
    · exact False.elim (q3 u9)
    · exact q4
    · exact False.elim (q5 u10)
  rcases h22220 with q0 | q1 | q2
  · exact False.elim (u11 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (u7 q2)

theorem step24731 (p1325 p1332 p1338 p1341 p1342 p1343 p1344 p1345 : Prop)
    (h8082 : p1338 ∨ p1341)
    (h8083 : p1338 ∨ p1342)
    (h8084 : p1338 ∨ p1343)
    (h8085 : p1338 ∨ p1344)
    (h8086 : p1338 ∨ p1345)
    (h8008 : p1325 ∨ p1332 ∨ (¬ p1341) ∨ (¬ p1342) ∨ (¬ p1343) ∨ (¬ p1344) ∨ (¬ p1345)) : p1338 ∨ p1332 ∨ p1325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1338) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1332) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1341 := by
    rcases h8082 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1342 := by
    rcases h8083 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1343 := by
    rcases h8084 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1344 := by
    rcases h8085 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1345 := by
    rcases h8086 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8008 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24732 (p1325 p1332 p1336 p1337 p1338 p1339 p1340 p1343 : Prop)
    (h24731 : p1338 ∨ p1332 ∨ p1325)
    (h8074 : p1336 ∨ p1343)
    (h8079 : p1337 ∨ p1343)
    (h8089 : p1339 ∨ p1343)
    (h8094 : p1340 ∨ p1343)
    (h7983 : p1325 ∨ p1332 ∨ (¬ p1336) ∨ (¬ p1337) ∨ (¬ p1338) ∨ (¬ p1339) ∨ (¬ p1340)) : p1343 ∨ p1332 ∨ p1325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1343) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1332) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1338 := by
    rcases h24731 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1336 := by
    rcases h8074 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1337 := by
    rcases h8079 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1339 := by
    rcases h8089 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1340 := by
    rcases h8094 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7983 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24733 (p1325 p1332 p1336 p1337 p1338 p1339 p1340 p1344 : Prop)
    (h24731 : p1338 ∨ p1332 ∨ p1325)
    (h8075 : p1336 ∨ p1344)
    (h8080 : p1337 ∨ p1344)
    (h8090 : p1339 ∨ p1344)
    (h8095 : p1340 ∨ p1344)
    (h7983 : p1325 ∨ p1332 ∨ (¬ p1336) ∨ (¬ p1337) ∨ (¬ p1338) ∨ (¬ p1339) ∨ (¬ p1340)) : p1344 ∨ p1332 ∨ p1325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1344) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1332) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1338 := by
    rcases h24731 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1336 := by
    rcases h8075 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1337 := by
    rcases h8080 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1339 := by
    rcases h8090 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1340 := by
    rcases h8095 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7983 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24734 (p1325 p1332 p1336 p1337 p1338 p1339 p1340 p1345 : Prop)
    (h24731 : p1338 ∨ p1332 ∨ p1325)
    (h8076 : p1336 ∨ p1345)
    (h8081 : p1337 ∨ p1345)
    (h8091 : p1339 ∨ p1345)
    (h8096 : p1340 ∨ p1345)
    (h7983 : p1325 ∨ p1332 ∨ (¬ p1336) ∨ (¬ p1337) ∨ (¬ p1338) ∨ (¬ p1339) ∨ (¬ p1340)) : p1345 ∨ p1332 ∨ p1325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1345) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1332) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1338 := by
    rcases h24731 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1336 := by
    rcases h8076 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1337 := by
    rcases h8081 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1339 := by
    rcases h8091 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1340 := by
    rcases h8096 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7983 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24735 (p1325 p1332 p1336 p1337 p1338 p1339 p1340 p1341 : Prop)
    (h24731 : p1338 ∨ p1332 ∨ p1325)
    (h8072 : p1336 ∨ p1341)
    (h8077 : p1337 ∨ p1341)
    (h8087 : p1339 ∨ p1341)
    (h8092 : p1340 ∨ p1341)
    (h7983 : p1325 ∨ p1332 ∨ (¬ p1336) ∨ (¬ p1337) ∨ (¬ p1338) ∨ (¬ p1339) ∨ (¬ p1340)) : p1341 ∨ p1332 ∨ p1325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1341) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1332) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1338 := by
    rcases h24731 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1336 := by
    rcases h8072 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1337 := by
    rcases h8077 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1339 := by
    rcases h8087 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1340 := by
    rcases h8092 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7983 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24736 (p1325 p1332 p1336 p1337 p1338 p1339 p1340 p1341 p1342 p1343 p1344 p1345 : Prop)
    (h24731 : p1338 ∨ p1332 ∨ p1325)
    (h24732 : p1343 ∨ p1332 ∨ p1325)
    (h24733 : p1344 ∨ p1332 ∨ p1325)
    (h24734 : p1345 ∨ p1332 ∨ p1325)
    (h24735 : p1341 ∨ p1332 ∨ p1325)
    (h8008 : p1325 ∨ p1332 ∨ (¬ p1341) ∨ (¬ p1342) ∨ (¬ p1343) ∨ (¬ p1344) ∨ (¬ p1345))
    (h8073 : p1336 ∨ p1342)
    (h8078 : p1337 ∨ p1342)
    (h8088 : p1339 ∨ p1342)
    (h8093 : p1340 ∨ p1342)
    (h7983 : p1325 ∨ p1332 ∨ (¬ p1336) ∨ (¬ p1337) ∨ (¬ p1338) ∨ (¬ p1339) ∨ (¬ p1340)) : p1332 ∨ p1325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1332) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr hu)
  have u2 : p1338 := by
    rcases h24731 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1343 := by
    rcases h24732 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1344 := by
    rcases h24733 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1345 := by
    rcases h24734 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p1341 := by
    rcases h24735 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p1342) := by
    rcases h8008 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u6)
    · exact q3
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u5)
  have u8 : p1336 := by
    rcases h8073 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p1337 := by
    rcases h8078 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p1339 := by
    rcases h8088 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p1340 := by
    rcases h8093 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h7983 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step24737 (p362 p363 p371 p372 p373 p374 p375 p380 : Prop)
    (h2058 : p371 ∨ p380)
    (h2063 : p372 ∨ p380)
    (h2068 : p373 ∨ p380)
    (h2073 : p374 ∨ p380)
    (h2078 : p375 ∨ p380)
    (h1956 : p362 ∨ p363 ∨ (¬ p371) ∨ (¬ p372) ∨ (¬ p373) ∨ (¬ p374) ∨ (¬ p375)) : p380 ∨ p363 ∨ p362 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p380) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p363) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p362) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p371 := by
    rcases h2058 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p372 := by
    rcases h2063 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p373 := by
    rcases h2068 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p374 := by
    rcases h2073 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p375 := by
    rcases h2078 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1956 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24738 (p362 p363 p371 p376 p377 p378 p379 p380 : Prop)
    (h24737 : p380 ∨ p363 ∨ p362)
    (h2054 : p371 ∨ p376)
    (h2055 : p371 ∨ p377)
    (h2056 : p371 ∨ p378)
    (h2057 : p371 ∨ p379)
    (h1981 : p362 ∨ p363 ∨ (¬ p376) ∨ (¬ p377) ∨ (¬ p378) ∨ (¬ p379) ∨ (¬ p380)) : p371 ∨ p363 ∨ p362 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p371) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p363) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p362) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p380 := by
    rcases h24737 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p376 := by
    rcases h2054 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p377 := by
    rcases h2055 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p378 := by
    rcases h2056 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p379 := by
    rcases h2057 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1981 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step24739 (p362 p363 p372 p376 p377 p378 p379 p380 : Prop)
    (h24737 : p380 ∨ p363 ∨ p362)
    (h2059 : p372 ∨ p376)
    (h2060 : p372 ∨ p377)
    (h2061 : p372 ∨ p378)
    (h2062 : p372 ∨ p379)
    (h1981 : p362 ∨ p363 ∨ (¬ p376) ∨ (¬ p377) ∨ (¬ p378) ∨ (¬ p379) ∨ (¬ p380)) : p372 ∨ p363 ∨ p362 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p372) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p363) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p362) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p380 := by
    rcases h24737 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p376 := by
    rcases h2059 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p377 := by
    rcases h2060 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p378 := by
    rcases h2061 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p379 := by
    rcases h2062 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1981 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step24740 (p362 p363 p373 p376 p377 p378 p379 p380 : Prop)
    (h24737 : p380 ∨ p363 ∨ p362)
    (h2064 : p373 ∨ p376)
    (h2065 : p373 ∨ p377)
    (h2066 : p373 ∨ p378)
    (h2067 : p373 ∨ p379)
    (h1981 : p362 ∨ p363 ∨ (¬ p376) ∨ (¬ p377) ∨ (¬ p378) ∨ (¬ p379) ∨ (¬ p380)) : p373 ∨ p363 ∨ p362 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p373) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p363) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p362) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p380 := by
    rcases h24737 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p376 := by
    rcases h2064 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p377 := by
    rcases h2065 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p378 := by
    rcases h2066 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p379 := by
    rcases h2067 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1981 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step24741 (p362 p363 p374 p376 p377 p378 p379 p380 : Prop)
    (h24737 : p380 ∨ p363 ∨ p362)
    (h2069 : p374 ∨ p376)
    (h2070 : p374 ∨ p377)
    (h2071 : p374 ∨ p378)
    (h2072 : p374 ∨ p379)
    (h1981 : p362 ∨ p363 ∨ (¬ p376) ∨ (¬ p377) ∨ (¬ p378) ∨ (¬ p379) ∨ (¬ p380)) : p374 ∨ p363 ∨ p362 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p374) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p363) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p362) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p380 := by
    rcases h24737 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p376 := by
    rcases h2069 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p377 := by
    rcases h2070 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p378 := by
    rcases h2071 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p379 := by
    rcases h2072 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1981 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step24742 (p362 p363 p371 p372 p373 p374 p375 p376 p377 p378 p379 p380 : Prop)
    (h24737 : p380 ∨ p363 ∨ p362)
    (h24738 : p371 ∨ p363 ∨ p362)
    (h24739 : p372 ∨ p363 ∨ p362)
    (h24740 : p373 ∨ p363 ∨ p362)
    (h24741 : p374 ∨ p363 ∨ p362)
    (h1956 : p362 ∨ p363 ∨ (¬ p371) ∨ (¬ p372) ∨ (¬ p373) ∨ (¬ p374) ∨ (¬ p375))
    (h2074 : p375 ∨ p376)
    (h2075 : p375 ∨ p377)
    (h2076 : p375 ∨ p378)
    (h2077 : p375 ∨ p379)
    (h1981 : p362 ∨ p363 ∨ (¬ p376) ∨ (¬ p377) ∨ (¬ p378) ∨ (¬ p379) ∨ (¬ p380)) : p363 ∨ p362 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p363) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p362) := fun hu => hn (Or.inr hu)
  have u2 : p380 := by
    rcases h24737 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p371 := by
    rcases h24738 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p372 := by
    rcases h24739 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p373 := by
    rcases h24740 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p374 := by
    rcases h24741 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p375) := by
    rcases h1956 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p376 := by
    rcases h2074 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p377 := by
    rcases h2075 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p378 := by
    rcases h2076 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p379 := by
    rcases h2077 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h1981 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u2)

theorem step24743 (p239 p242 p245 p246 p247 p248 p249 p253 : Prop)
    (h1283 : p245 ∨ p253)
    (h1288 : p246 ∨ p253)
    (h1293 : p247 ∨ p253)
    (h1298 : p248 ∨ p253)
    (h1303 : p249 ∨ p253)
    (h1196 : p239 ∨ p242 ∨ (¬ p245) ∨ (¬ p246) ∨ (¬ p247) ∨ (¬ p248) ∨ (¬ p249)) : p253 ∨ p242 ∨ p239 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p253) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p242) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p239) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p245 := by
    rcases h1283 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p246 := by
    rcases h1288 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p247 := by
    rcases h1293 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p248 := by
    rcases h1298 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p249 := by
    rcases h1303 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1196 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24749 (p237 p239 p249 p250 p251 p252 p253 p254 : Prop)
    (h1300 : p249 ∨ p250)
    (h1301 : p249 ∨ p251)
    (h1302 : p249 ∨ p252)
    (h1304 : p249 ∨ p254)
    (h1222 : p237 ∨ p239 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : p249 ∨ (¬ p253) ∨ p239 ∨ p237 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p249) := fun hu => hn (Or.inl hu)
  have u1 : p253 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p239) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p237) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p250 := by
    rcases h1300 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p251 := by
    rcases h1301 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p252 := by
    rcases h1302 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p254 := by
    rcases h1304 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1222 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step24750 (p185 p237 p239 p242 p245 p246 p247 p248 p249 p253 p254 : Prop)
    (h22284 : p242 ∨ p185)
    (h1179 : (¬ p185) ∨ (¬ p237))
    (h24743 : p253 ∨ p242 ∨ p239)
    (h24749 : p249 ∨ (¬ p253) ∨ p239 ∨ p237)
    (h1284 : p245 ∨ p254)
    (h1289 : p246 ∨ p254)
    (h1294 : p247 ∨ p254)
    (h1299 : p248 ∨ p254)
    (h1196 : p239 ∨ p242 ∨ (¬ p245) ∨ (¬ p246) ∨ (¬ p247) ∨ (¬ p248) ∨ (¬ p249)) : p254 ∨ p239 ∨ p242 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p254) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p239) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p242) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p185 := by
    rcases h22284 with q0 | q1
    · exact False.elim (u2 q0)
    · exact q1
  have u4 : (¬ p237) := by
    rcases h1179 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  have u5 : p253 := by
    rcases h24743 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u2 q1)
    · exact False.elim (u1 q2)
  have u6 : p249 := by
    rcases h24749 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u5)
    · exact False.elim (u1 q2)
    · exact False.elim (u4 q3)
  have u7 : p245 := by
    rcases h1284 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p246 := by
    rcases h1289 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p247 := by
    rcases h1294 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p248 := by
    rcases h1299 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1196 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u6)

theorem step24751 (p185 p237 p239 p242 p245 p246 p247 p248 p249 p250 p253 : Prop)
    (h22284 : p242 ∨ p185)
    (h1179 : (¬ p185) ∨ (¬ p237))
    (h24743 : p253 ∨ p242 ∨ p239)
    (h24749 : p249 ∨ (¬ p253) ∨ p239 ∨ p237)
    (h1280 : p245 ∨ p250)
    (h1285 : p246 ∨ p250)
    (h1290 : p247 ∨ p250)
    (h1295 : p248 ∨ p250)
    (h1196 : p239 ∨ p242 ∨ (¬ p245) ∨ (¬ p246) ∨ (¬ p247) ∨ (¬ p248) ∨ (¬ p249)) : p250 ∨ p239 ∨ p242 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p250) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p239) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p242) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p185 := by
    rcases h22284 with q0 | q1
    · exact False.elim (u2 q0)
    · exact q1
  have u4 : (¬ p237) := by
    rcases h1179 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  have u5 : p253 := by
    rcases h24743 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u2 q1)
    · exact False.elim (u1 q2)
  have u6 : p249 := by
    rcases h24749 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u5)
    · exact False.elim (u1 q2)
    · exact False.elim (u4 q3)
  have u7 : p245 := by
    rcases h1280 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p246 := by
    rcases h1285 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p247 := by
    rcases h1290 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p248 := by
    rcases h1295 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1196 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u6)

theorem step24752 (p185 p237 p239 p242 p245 p246 p247 p248 p249 p251 p253 : Prop)
    (h22284 : p242 ∨ p185)
    (h1179 : (¬ p185) ∨ (¬ p237))
    (h24743 : p253 ∨ p242 ∨ p239)
    (h24749 : p249 ∨ (¬ p253) ∨ p239 ∨ p237)
    (h1281 : p245 ∨ p251)
    (h1286 : p246 ∨ p251)
    (h1291 : p247 ∨ p251)
    (h1296 : p248 ∨ p251)
    (h1196 : p239 ∨ p242 ∨ (¬ p245) ∨ (¬ p246) ∨ (¬ p247) ∨ (¬ p248) ∨ (¬ p249)) : p251 ∨ p239 ∨ p242 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p251) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p239) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p242) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p185 := by
    rcases h22284 with q0 | q1
    · exact False.elim (u2 q0)
    · exact q1
  have u4 : (¬ p237) := by
    rcases h1179 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  have u5 : p253 := by
    rcases h24743 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u2 q1)
    · exact False.elim (u1 q2)
  have u6 : p249 := by
    rcases h24749 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u5)
    · exact False.elim (u1 q2)
    · exact False.elim (u4 q3)
  have u7 : p245 := by
    rcases h1281 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p246 := by
    rcases h1286 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p247 := by
    rcases h1291 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p248 := by
    rcases h1296 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1196 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u6)

theorem step24753 (p185 p237 p239 p242 p245 p246 p247 p248 p249 p250 p251 p252 p253 p254 : Prop)
    (h22284 : p242 ∨ p185)
    (h1179 : (¬ p185) ∨ (¬ p237))
    (h24743 : p253 ∨ p242 ∨ p239)
    (h24749 : p249 ∨ (¬ p253) ∨ p239 ∨ p237)
    (h24750 : p254 ∨ p239 ∨ p242)
    (h24751 : p250 ∨ p239 ∨ p242)
    (h24752 : p251 ∨ p239 ∨ p242)
    (h1222 : p237 ∨ p239 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254))
    (h1282 : p245 ∨ p252)
    (h1287 : p246 ∨ p252)
    (h1292 : p247 ∨ p252)
    (h1297 : p248 ∨ p252)
    (h1196 : p239 ∨ p242 ∨ (¬ p245) ∨ (¬ p246) ∨ (¬ p247) ∨ (¬ p248) ∨ (¬ p249)) : p239 ∨ p242 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p239) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p242) := fun hu => hn (Or.inr hu)
  have u2 : p185 := by
    rcases h22284 with q0 | q1
    · exact False.elim (u1 q0)
    · exact q1
  have u3 : (¬ p237) := by
    rcases h1179 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u4 : p253 := by
    rcases h24743 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u5 : p249 := by
    rcases h24749 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u4)
    · exact False.elim (u0 q2)
    · exact False.elim (u3 q3)
  have u6 : p254 := by
    rcases h24750 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : p250 := by
    rcases h24751 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u8 : p251 := by
    rcases h24752 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u9 : (¬ p252) := by
    rcases h1222 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u7)
    · exact False.elim (q3 u8)
    · exact q4
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u6)
  have u10 : p245 := by
    rcases h1282 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  have u11 : p246 := by
    rcases h1287 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  have u12 : p247 := by
    rcases h1292 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  have u13 : p248 := by
    rcases h1297 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h1196 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u12)
  · exact False.elim (q5 u13)
  · exact False.elim (q6 u5)

theorem step24754 (p1037 p1041 p1045 p1046 p1047 p1048 p1049 p1053 : Prop)
    (h6199 : p1045 ∨ p1053)
    (h6204 : p1046 ∨ p1053)
    (h6209 : p1047 ∨ p1053)
    (h6214 : p1048 ∨ p1053)
    (h6219 : p1049 ∨ p1053)
    (h6096 : p1037 ∨ p1041 ∨ (¬ p1045) ∨ (¬ p1046) ∨ (¬ p1047) ∨ (¬ p1048) ∨ (¬ p1049)) : p1053 ∨ p1037 ∨ p1041 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1053) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1037) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1041) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1045 := by
    rcases h6199 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1046 := by
    rcases h6204 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1047 := by
    rcases h6209 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1048 := by
    rcases h6214 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1049 := by
    rcases h6219 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6096 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24755 (p12 p1037 p1045 p1050 p1051 p1052 p1053 p1054 : Prop)
    (h6196 : p1045 ∨ p1050)
    (h6197 : p1045 ∨ p1051)
    (h6198 : p1045 ∨ p1052)
    (h6200 : p1045 ∨ p1054)
    (h6123 : p12 ∨ p1037 ∨ (¬ p1050) ∨ (¬ p1051) ∨ (¬ p1052) ∨ (¬ p1053) ∨ (¬ p1054)) : p1045 ∨ (¬ p1053) ∨ p1037 ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1045) := fun hu => hn (Or.inl hu)
  have u1 : p1053 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1037) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1050 := by
    rcases h6196 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1051 := by
    rcases h6197 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1052 := by
    rcases h6198 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1054 := by
    rcases h6200 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6123 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step24756 (p12 p1037 p1046 p1050 p1051 p1052 p1053 p1054 : Prop)
    (h6201 : p1046 ∨ p1050)
    (h6202 : p1046 ∨ p1051)
    (h6203 : p1046 ∨ p1052)
    (h6205 : p1046 ∨ p1054)
    (h6123 : p12 ∨ p1037 ∨ (¬ p1050) ∨ (¬ p1051) ∨ (¬ p1052) ∨ (¬ p1053) ∨ (¬ p1054)) : p1046 ∨ (¬ p1053) ∨ p1037 ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1046) := fun hu => hn (Or.inl hu)
  have u1 : p1053 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1037) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1050 := by
    rcases h6201 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1051 := by
    rcases h6202 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1052 := by
    rcases h6203 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1054 := by
    rcases h6205 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6123 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step24757 (p12 p1037 p1047 p1050 p1051 p1052 p1053 p1054 : Prop)
    (h6206 : p1047 ∨ p1050)
    (h6207 : p1047 ∨ p1051)
    (h6208 : p1047 ∨ p1052)
    (h6210 : p1047 ∨ p1054)
    (h6123 : p12 ∨ p1037 ∨ (¬ p1050) ∨ (¬ p1051) ∨ (¬ p1052) ∨ (¬ p1053) ∨ (¬ p1054)) : p1047 ∨ (¬ p1053) ∨ p1037 ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1047) := fun hu => hn (Or.inl hu)
  have u1 : p1053 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1037) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1050 := by
    rcases h6206 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1051 := by
    rcases h6207 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1052 := by
    rcases h6208 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1054 := by
    rcases h6210 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6123 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step24758 (p12 p1037 p1048 p1050 p1051 p1052 p1053 p1054 : Prop)
    (h6211 : p1048 ∨ p1050)
    (h6212 : p1048 ∨ p1051)
    (h6213 : p1048 ∨ p1052)
    (h6215 : p1048 ∨ p1054)
    (h6123 : p12 ∨ p1037 ∨ (¬ p1050) ∨ (¬ p1051) ∨ (¬ p1052) ∨ (¬ p1053) ∨ (¬ p1054)) : p1048 ∨ (¬ p1053) ∨ p1037 ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1048) := fun hu => hn (Or.inl hu)
  have u1 : p1053 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1037) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1050 := by
    rcases h6211 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1051 := by
    rcases h6212 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1052 := by
    rcases h6213 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1054 := by
    rcases h6215 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6123 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step24759 (p12 p1037 p1045 p1046 p1047 p1048 p1049 p1050 p1051 p1052 p1053 p1054 : Prop)
    (h24755 : p1045 ∨ (¬ p1053) ∨ p1037 ∨ p12)
    (h24756 : p1046 ∨ (¬ p1053) ∨ p1037 ∨ p12)
    (h24757 : p1047 ∨ (¬ p1053) ∨ p1037 ∨ p12)
    (h24758 : p1048 ∨ (¬ p1053) ∨ p1037 ∨ p12)
    (h6098 : p12 ∨ p1037 ∨ (¬ p1045) ∨ (¬ p1046) ∨ (¬ p1047) ∨ (¬ p1048) ∨ (¬ p1049))
    (h6216 : p1049 ∨ p1050)
    (h6217 : p1049 ∨ p1051)
    (h6218 : p1049 ∨ p1052)
    (h6220 : p1049 ∨ p1054)
    (h6123 : p12 ∨ p1037 ∨ (¬ p1050) ∨ (¬ p1051) ∨ (¬ p1052) ∨ (¬ p1053) ∨ (¬ p1054)) : (¬ p1053) ∨ p1037 ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1053 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1037) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p12) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1045 := by
    rcases h24755 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u4 : p1046 := by
    rcases h24756 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u5 : p1047 := by
    rcases h24757 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u6 : p1048 := by
    rcases h24758 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u7 : (¬ p1049) := by
    rcases h6098 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p1050 := by
    rcases h6216 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p1051 := by
    rcases h6217 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p1052 := by
    rcases h6218 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p1054 := by
    rcases h6220 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h6123 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u11)

theorem step24760 (p12 p544 p664 p980 p983 p1037 p1041 p1053 p1465 : Prop)
    (h20687 : p980 ∨ p983)
    (h15131 : p980 ∨ (¬ p1041) ∨ (¬ p1465))
    (h19165 : (¬ p544) ∨ (¬ p664) ∨ (¬ p983) ∨ (¬ p1037) ∨ (¬ p1465))
    (h24754 : p1053 ∨ p1037 ∨ p1041)
    (h24759 : (¬ p1053) ∨ p1037 ∨ p12) : (¬ p1465) ∨ p980 ∨ p12 ∨ (¬ p664) ∨ (¬ p544) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p983 := by
    rcases h20687 with q0 | q1
    · exact False.elim (u1 q0)
    · exact q1
  have u6 : (¬ p1041) := by
    rcases h15131 with q0 | q1 | q2
    · exact False.elim (u1 q0)
    · exact q1
    · exact False.elim (q2 u0)
  have u7 : (¬ p1037) := by
    rcases h19165 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u4)
    · exact False.elim (q1 u3)
    · exact False.elim (q2 u5)
    · exact q3
    · exact False.elim (q4 u0)
  have u8 : p1053 := by
    rcases h24754 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u7 q1)
    · exact False.elim (u6 q2)
  rcases h24759 with q0 | q1 | q2
  · exact False.elim (q0 u8)
  · exact False.elim (u7 q1)
  · exact False.elim (u2 q2)

theorem step24761 (p12 p1038 p1049 p1050 p1051 p1052 p1053 p1054 : Prop)
    (h6216 : p1049 ∨ p1050)
    (h6217 : p1049 ∨ p1051)
    (h6218 : p1049 ∨ p1052)
    (h6220 : p1049 ∨ p1054)
    (h6128 : p12 ∨ p1038 ∨ (¬ p1050) ∨ (¬ p1051) ∨ (¬ p1052) ∨ (¬ p1053) ∨ (¬ p1054)) : p1049 ∨ (¬ p1053) ∨ p1038 ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1049) := fun hu => hn (Or.inl hu)
  have u1 : p1053 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1038) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1050 := by
    rcases h6216 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1051 := by
    rcases h6217 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1052 := by
    rcases h6218 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1054 := by
    rcases h6220 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6128 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step24770 (p17 p224 p256 p258 p264 p287 p304 p346 p840 : Prop)
    (h10652 : (¬ p17) ∨ (¬ p256))
    (h21163 : p264 ∨ p256)
    (h20100 : (¬ p17) ∨ (¬ p224) ∨ (¬ p258) ∨ (¬ p346))
    (h16863 : (¬ p264) ∨ (¬ p287) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p840))
    (h21436 : p258 ∨ p287) : (¬ p346) ∨ (¬ p224) ∨ (¬ p840) ∨ (¬ p304) ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p256) := by
    rcases h10652 with q0 | q1
    · exact False.elim (q0 u4)
    · exact q1
  have u6 : p264 := by
    rcases h21163 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u7 : (¬ p258) := by
    rcases h20100 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u4)
    · exact False.elim (q1 u1)
    · exact q2
    · exact False.elim (q3 u0)
  have u8 : (¬ p287) := by
    rcases h16863 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u6)
    · exact q1
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u2)
  rcases h21436 with q0 | q1
  · exact False.elim (u7 q0)
  · exact False.elim (u8 q1)

theorem step24771 (p11 p258 p287 p1077 p1079 p1116 : Prop)
    (h21436 : p258 ∨ p287)
    (h21866 : p258 ∨ (¬ p1077) ∨ (¬ p11))
    (h12419 : (¬ p11) ∨ (¬ p287) ∨ (¬ p1079) ∨ (¬ p1116))
    (h22852 : p1079 ∨ p1077) : p258 ∨ (¬ p1116) ∨ (¬ p11) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p258) := fun hu => hn (Or.inl hu)
  have u1 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p287 := by
    rcases h21436 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : (¬ p1077) := by
    rcases h21866 with q0 | q1 | q2
    · exact False.elim (u0 q0)
    · exact q1
    · exact False.elim (q2 u2)
  have u5 : (¬ p1079) := by
    rcases h12419 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u2)
    · exact False.elim (q1 u3)
    · exact q2
    · exact False.elim (q3 u1)
  rcases h22852 with q0 | q1
  · exact False.elim (u5 q0)
  · exact False.elim (u4 q1)

theorem step24772 (p301 p519 p523 p524 p525 p526 p527 : Prop)
    (h2969 : p524 ∨ p527)
    (h2974 : p525 ∨ p527)
    (h2979 : p526 ∨ p527)
    (h24718 : (¬ p526) ∨ p519 ∨ p301 ∨ (¬ p523) ∨ (¬ p525) ∨ (¬ p524)) : p527 ∨ (¬ p523) ∨ p519 ∨ p301 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p527) := fun hu => hn (Or.inl hu)
  have u1 : p523 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p519) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p301) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p524 := by
    rcases h2969 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p525 := by
    rcases h2974 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p526 := by
    rcases h2979 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h24718 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u6)
  · exact False.elim (u2 q1)
  · exact False.elim (u3 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u4)

theorem step24773 (p301 p519 p523 p524 p525 p526 p528 : Prop)
    (h2970 : p524 ∨ p528)
    (h2975 : p525 ∨ p528)
    (h2980 : p526 ∨ p528)
    (h24718 : (¬ p526) ∨ p519 ∨ p301 ∨ (¬ p523) ∨ (¬ p525) ∨ (¬ p524)) : p528 ∨ (¬ p523) ∨ p519 ∨ p301 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p528) := fun hu => hn (Or.inl hu)
  have u1 : p523 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p519) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p301) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p524 := by
    rcases h2970 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p525 := by
    rcases h2975 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p526 := by
    rcases h2980 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h24718 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u6)
  · exact False.elim (u2 q1)
  · exact False.elim (u3 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u4)

theorem step24774 (p301 p519 p523 p524 p525 p526 p529 : Prop)
    (h2971 : p524 ∨ p529)
    (h2976 : p525 ∨ p529)
    (h2981 : p526 ∨ p529)
    (h24718 : (¬ p526) ∨ p519 ∨ p301 ∨ (¬ p523) ∨ (¬ p525) ∨ (¬ p524)) : p529 ∨ (¬ p523) ∨ p519 ∨ p301 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p529) := fun hu => hn (Or.inl hu)
  have u1 : p523 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p519) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p301) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p524 := by
    rcases h2971 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p525 := by
    rcases h2976 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p526 := by
    rcases h2981 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h24718 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u6)
  · exact False.elim (u2 q1)
  · exact False.elim (u3 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u4)

theorem step24775 (p301 p519 p523 p524 p525 p526 p527 p528 p529 p530 p531 : Prop)
    (h21665 : p523 ∨ (¬ p531) ∨ p519 ∨ p301)
    (h24772 : p527 ∨ (¬ p523) ∨ p519 ∨ p301)
    (h24773 : p528 ∨ (¬ p523) ∨ p519 ∨ p301)
    (h24774 : p529 ∨ (¬ p523) ∨ p519 ∨ p301)
    (h2895 : p301 ∨ p519 ∨ (¬ p527) ∨ (¬ p528) ∨ (¬ p529) ∨ (¬ p530) ∨ (¬ p531))
    (h2972 : p524 ∨ p530)
    (h2977 : p525 ∨ p530)
    (h2982 : p526 ∨ p530)
    (h24718 : (¬ p526) ∨ p519 ∨ p301 ∨ (¬ p523) ∨ (¬ p525) ∨ (¬ p524)) : (¬ p531) ∨ p519 ∨ p301 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p531 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p519) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p301) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p523 := by
    rcases h21665 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u4 : p527 := by
    rcases h24772 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u5 : p528 := by
    rcases h24773 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u6 : p529 := by
    rcases h24774 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u7 : (¬ p530) := by
    rcases h2895 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u6)
    · exact q5
    · exact False.elim (q6 u0)
  have u8 : p524 := by
    rcases h2972 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p525 := by
    rcases h2977 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p526 := by
    rcases h2982 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h24718 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u10)
  · exact False.elim (u1 q1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u8)

theorem step24776 (p301 p519 p523 p524 p525 p526 p531 : Prop)
    (h24775 : (¬ p531) ∨ p519 ∨ p301)
    (h2968 : p523 ∨ p531)
    (h2973 : p524 ∨ p531)
    (h2978 : p525 ∨ p531)
    (h2983 : p526 ∨ p531)
    (h24718 : (¬ p526) ∨ p519 ∨ p301 ∨ (¬ p523) ∨ (¬ p525) ∨ (¬ p524)) : p519 ∨ p301 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p519) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p301) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p531) := by
    rcases h24775 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p523 := by
    rcases h2968 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : p524 := by
    rcases h2973 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p525 := by
    rcases h2978 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p526 := by
    rcases h2983 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h24718 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u6)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u4)

theorem step24786 (p12 p39 p69 p88 p229 p665 p790 p814 p858 p879 p883 p1096 p1385 : Prop)
    (h24705 : (¬ p790) ∨ (¬ p39) ∨ (¬ p1385) ∨ (¬ p69))
    (h10795 : (¬ p69) ∨ (¬ p879) ∨ (¬ p1096))
    (h20735 : p790 ∨ p814)
    (h23012 : p883 ∨ p879 ∨ p229)
    (h19170 : (¬ p12) ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p665) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p883) ∨ (¬ p1096)) : (¬ p69) ∨ (¬ p1096) ∨ (¬ p1385) ∨ (¬ p665) ∨ (¬ p12) ∨ p229 ∨ (¬ p39) ∨ (¬ p88) ∨ (¬ p858) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1385 := by
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
  have u5 : (¬ p229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p790) := by
    rcases h24705 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u6)
    · exact False.elim (q2 u2)
    · exact False.elim (q3 u0)
  have u10 : (¬ p879) := by
    rcases h10795 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (q2 u1)
  have u11 : p814 := by
    rcases h20735 with q0 | q1
    · exact False.elim (u9 q0)
    · exact q1
  have u12 : p883 := by
    rcases h23012 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u10 q1)
    · exact False.elim (u5 q2)
  rcases h19170 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u12)
  · exact False.elim (q8 u1)

theorem step24787 (p189 p237 p980 p1118 p1122 p1346 p1465 p1508 : Prop)
    (h19183 : (¬ p189) ∨ (¬ p1346) ∨ (¬ p1465) ∨ (¬ p1508))
    (h11633 : (¬ p980) ∨ (¬ p1118) ∨ (¬ p1508))
    (h12098 : (¬ p237) ∨ (¬ p1122) ∨ p1346)
    (h22204 : p1122 ∨ p1118) : (¬ p1508) ∨ (¬ p189) ∨ (¬ p237) ∨ (¬ p1465) ∨ (¬ p980) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p1346) := by
    rcases h19183 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u1)
    · exact q1
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u0)
  have u6 : (¬ p1118) := by
    rcases h11633 with q0 | q1 | q2
    · exact False.elim (q0 u4)
    · exact q1
    · exact False.elim (q2 u0)
  have u7 : (¬ p1122) := by
    rcases h12098 with q0 | q1 | q2
    · exact False.elim (q0 u2)
    · exact q1
    · exact False.elim (u5 q2)
  rcases h22204 with q0 | q1
  · exact False.elim (u7 q0)
  · exact False.elim (u6 q1)

theorem step24788 (p103 p124 p125 p169 p189 p225 p237 p242 p304 p305 p323 p344 p345 p346 p348 p350 p362 p536 p537 p544 p726 p727 p737 p756 p769 p940 p1584 : Prop)
    (h15559 : p125 ∨ (¬ p304) ∨ (¬ p345))
    (h21358 : p345 ∨ p344)
    (h7033 : (¬ p344) ∨ (¬ p346))
    (h24340 : p348 ∨ p346)
    (h21667 : p350 ∨ p345)
    (h21038 : p125 ∨ p362)
    (h6741 : (¬ p124) ∨ (¬ p304))
    (h21498 : p305 ∨ p124)
    (h12216 : p225 ∨ (¬ p737) ∨ (¬ p940))
    (h17384 : (¬ p237) ∨ (¬ p537) ∨ (¬ p544) ∨ (¬ p940))
    (h23055 : p727 ∨ p737)
    (h23568 : p1584 ∨ p537)
    (h17394 : (¬ p304) ∨ (¬ p348) ∨ (¬ p362) ∨ (¬ p726) ∨ (¬ p727))
    (h19182 : (¬ p103) ∨ (¬ p169) ∨ (¬ p189) ∨ (¬ p242) ∨ (¬ p323) ∨ (¬ p536) ∨ (¬ p1584))
    (h21112 : p726 ∨ p756)
    (h20741 : p769 ∨ p536)
    (h16800 : (¬ p305) ∨ (¬ p350) ∨ (¬ p362) ∨ (¬ p756) ∨ (¬ p769)) : (¬ p940) ∨ (¬ p242) ∨ (¬ p189) ∨ (¬ p237) ∨ (¬ p103) ∨ (¬ p169) ∨ (¬ p323) ∨ p125 ∨ (¬ p544) ∨ p225 ∨ (¬ p304) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p242 := by
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
  have u4 : p103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p169 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : (¬ p345) := by
    rcases h15559 with q0 | q1 | q2
    · exact False.elim (u7 q0)
    · exact False.elim (q1 u10)
    · exact q2
  have u12 : p344 := by
    rcases h21358 with q0 | q1
    · exact False.elim (u11 q0)
    · exact q1
  have u13 : (¬ p346) := by
    rcases h7033 with q0 | q1
    · exact False.elim (q0 u12)
    · exact q1
  have u14 : p348 := by
    rcases h24340 with q0 | q1
    · exact q0
    · exact False.elim (u13 q1)
  have u15 : p350 := by
    rcases h21667 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  have u16 : p362 := by
    rcases h21038 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u17 : (¬ p124) := by
    rcases h6741 with q0 | q1
    · exact q0
    · exact False.elim (q1 u10)
  have u18 : p305 := by
    rcases h21498 with q0 | q1
    · exact q0
    · exact False.elim (u17 q1)
  have u19 : (¬ p737) := by
    rcases h12216 with q0 | q1 | q2
    · exact False.elim (u9 q0)
    · exact q1
    · exact False.elim (q2 u0)
  have u20 : (¬ p537) := by
    rcases h17384 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u3)
    · exact q1
    · exact False.elim (q2 u8)
    · exact False.elim (q3 u0)
  have u21 : p727 := by
    rcases h23055 with q0 | q1
    · exact q0
    · exact False.elim (u19 q1)
  have u22 : p1584 := by
    rcases h23568 with q0 | q1
    · exact q0
    · exact False.elim (u20 q1)
  have u23 : (¬ p726) := by
    rcases h17394 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u10)
    · exact False.elim (q1 u14)
    · exact False.elim (q2 u16)
    · exact q3
    · exact False.elim (q4 u21)
  have u24 : (¬ p536) := by
    rcases h19182 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u4)
    · exact False.elim (q1 u5)
    · exact False.elim (q2 u2)
    · exact False.elim (q3 u1)
    · exact False.elim (q4 u6)
    · exact q5
    · exact False.elim (q6 u22)
  have u25 : p756 := by
    rcases h21112 with q0 | q1
    · exact False.elim (u23 q0)
    · exact q1
  have u26 : p769 := by
    rcases h20741 with q0 | q1
    · exact q0
    · exact False.elim (u24 q1)
  rcases h16800 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u18)
  · exact False.elim (q1 u15)
  · exact False.elim (q2 u16)
  · exact False.elim (q3 u25)
  · exact False.elim (q4 u26)

theorem step24789 (p12 p13 p14 p15 p135 p165 p169 p189 p227 p237 p265 p500 p532 p533 p534 p959 p961 p1076 p1116 p1226 p1452 : Prop)
    (h24665 : p500)
    (h6736 : (¬ p165) ∨ (¬ p189) ∨ (¬ p237))
    (h21921 : p165 ∨ p169)
    (h14625 : (¬ p12) ∨ (¬ p169) ∨ p1116)
    (h17551 : (¬ p189) ∨ (¬ p237) ∨ (¬ p1076) ∨ (¬ p1116))
    (h22593 : p1076 ∨ p13)
    (h20693 : p227 ∨ p959)
    (h21044 : p961 ∨ p227)
    (h20433 : (¬ p12) ∨ (¬ p13) ∨ (¬ p135) ∨ (¬ p169) ∨ (¬ p189) ∨ (¬ p237) ∨ (¬ p265) ∨ (¬ p959) ∨ (¬ p1226) ∨ (¬ p1452))
    (h17385 : (¬ p14) ∨ (¬ p15) ∨ (¬ p500) ∨ (¬ p532) ∨ (¬ p533) ∨ (¬ p534) ∨ (¬ p961))
    (h21329 : p1452 ∨ p532) : p227 ∨ (¬ p15) ∨ (¬ p1226) ∨ (¬ p533) ∨ (¬ p534) ∨ (¬ p12) ∨ (¬ p14) ∨ (¬ p135) ∨ (¬ p189) ∨ (¬ p265) ∨ (¬ p237) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p227) := fun hu => hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1226 := by
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
  have u5 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : p500 := by
    exact h24665
  have u12 : (¬ p165) := by
    rcases h6736 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u8)
    · exact False.elim (q2 u10)
  have u13 : p169 := by
    rcases h21921 with q0 | q1
    · exact False.elim (u12 q0)
    · exact q1
  have u14 : p1116 := by
    rcases h14625 with q0 | q1 | q2
    · exact False.elim (q0 u5)
    · exact False.elim (q1 u13)
    · exact q2
  have u15 : (¬ p1076) := by
    rcases h17551 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u8)
    · exact False.elim (q1 u10)
    · exact q2
    · exact False.elim (q3 u14)
  have u16 : p13 := by
    rcases h22593 with q0 | q1
    · exact False.elim (u15 q0)
    · exact q1
  have u17 : p959 := by
    rcases h20693 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u18 : p961 := by
    rcases h21044 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u19 : (¬ p1452) := by
    rcases h20433 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
    · exact False.elim (q0 u5)
    · exact False.elim (q1 u16)
    · exact False.elim (q2 u7)
    · exact False.elim (q3 u13)
    · exact False.elim (q4 u8)
    · exact False.elim (q5 u10)
    · exact False.elim (q6 u9)
    · exact False.elim (q7 u17)
    · exact False.elim (q8 u2)
    · exact q9
  have u20 : (¬ p532) := by
    rcases h17385 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u6)
    · exact False.elim (q1 u1)
    · exact False.elim (q2 u11)
    · exact q3
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u18)
  rcases h21329 with q0 | q1
  · exact False.elim (u19 q0)
  · exact False.elim (u20 q1)

theorem step24790 (p1291 p1292 p1300 p1301 p1302 p1303 p1304 p1305 : Prop)
    (h7830 : p1300 ∨ p1301)
    (h7831 : p1300 ∨ p1302)
    (h7833 : p1300 ∨ p1304)
    (h7834 : p1300 ∨ p1305)
    (h7755 : p1291 ∨ p1292 ∨ (¬ p1301) ∨ (¬ p1302) ∨ (¬ p1303) ∨ (¬ p1304) ∨ (¬ p1305)) : p1300 ∨ (¬ p1303) ∨ p1291 ∨ p1292 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1300) := fun hu => hn (Or.inl hu)
  have u1 : p1303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1291) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1292) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1301 := by
    rcases h7830 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1302 := by
    rcases h7831 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1304 := by
    rcases h7833 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1305 := by
    rcases h7834 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7755 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24791 (p1291 p1292 p1296 p1297 p1298 p1299 p1300 p1304 : Prop)
    (h7813 : p1296 ∨ p1304)
    (h7818 : p1297 ∨ p1304)
    (h7823 : p1298 ∨ p1304)
    (h7828 : p1299 ∨ p1304)
    (h7730 : p1291 ∨ p1292 ∨ (¬ p1296) ∨ (¬ p1297) ∨ (¬ p1298) ∨ (¬ p1299) ∨ (¬ p1300)) : p1304 ∨ (¬ p1300) ∨ p1291 ∨ p1292 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1304) := fun hu => hn (Or.inl hu)
  have u1 : p1300 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1291) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1292) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1296 := by
    rcases h7813 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1297 := by
    rcases h7818 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1298 := by
    rcases h7823 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1299 := by
    rcases h7828 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7730 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24792 (p1291 p1292 p1296 p1297 p1298 p1299 p1300 p1305 : Prop)
    (h7814 : p1296 ∨ p1305)
    (h7819 : p1297 ∨ p1305)
    (h7824 : p1298 ∨ p1305)
    (h7829 : p1299 ∨ p1305)
    (h7730 : p1291 ∨ p1292 ∨ (¬ p1296) ∨ (¬ p1297) ∨ (¬ p1298) ∨ (¬ p1299) ∨ (¬ p1300)) : p1305 ∨ (¬ p1300) ∨ p1291 ∨ p1292 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1305) := fun hu => hn (Or.inl hu)
  have u1 : p1300 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1291) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1292) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1296 := by
    rcases h7814 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1297 := by
    rcases h7819 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1298 := by
    rcases h7824 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1299 := by
    rcases h7829 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7730 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24793 (p1291 p1292 p1296 p1297 p1298 p1299 p1300 p1301 : Prop)
    (h7810 : p1296 ∨ p1301)
    (h7815 : p1297 ∨ p1301)
    (h7820 : p1298 ∨ p1301)
    (h7825 : p1299 ∨ p1301)
    (h7730 : p1291 ∨ p1292 ∨ (¬ p1296) ∨ (¬ p1297) ∨ (¬ p1298) ∨ (¬ p1299) ∨ (¬ p1300)) : p1301 ∨ (¬ p1300) ∨ p1291 ∨ p1292 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1301) := fun hu => hn (Or.inl hu)
  have u1 : p1300 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1291) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1292) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1296 := by
    rcases h7810 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1297 := by
    rcases h7815 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1298 := by
    rcases h7820 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1299 := by
    rcases h7825 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7730 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step24794 (p1291 p1292 p1296 p1297 p1298 p1299 p1300 p1301 p1302 p1303 p1304 p1305 : Prop)
    (h24790 : p1300 ∨ (¬ p1303) ∨ p1291 ∨ p1292)
    (h24791 : p1304 ∨ (¬ p1300) ∨ p1291 ∨ p1292)
    (h24792 : p1305 ∨ (¬ p1300) ∨ p1291 ∨ p1292)
    (h24793 : p1301 ∨ (¬ p1300) ∨ p1291 ∨ p1292)
    (h7755 : p1291 ∨ p1292 ∨ (¬ p1301) ∨ (¬ p1302) ∨ (¬ p1303) ∨ (¬ p1304) ∨ (¬ p1305))
    (h7811 : p1296 ∨ p1302)
    (h7816 : p1297 ∨ p1302)
    (h7821 : p1298 ∨ p1302)
    (h7826 : p1299 ∨ p1302)
    (h7730 : p1291 ∨ p1292 ∨ (¬ p1296) ∨ (¬ p1297) ∨ (¬ p1298) ∨ (¬ p1299) ∨ (¬ p1300)) : (¬ p1303) ∨ p1291 ∨ p1292 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1291) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1292) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1300 := by
    rcases h24790 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u4 : p1304 := by
    rcases h24791 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u5 : p1305 := by
    rcases h24792 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u6 : p1301 := by
    rcases h24793 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u7 : (¬ p1302) := by
    rcases h7755 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u6)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u5)
  have u8 : p1296 := by
    rcases h7811 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p1297 := by
    rcases h7816 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p1298 := by
    rcases h7821 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p1299 := by
    rcases h7826 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h7730 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u3)

theorem step24795 (p1291 p1292 p1296 p1297 p1298 p1299 p1300 p1303 : Prop)
    (h24794 : (¬ p1303) ∨ p1291 ∨ p1292)
    (h7812 : p1296 ∨ p1303)
    (h7817 : p1297 ∨ p1303)
    (h7822 : p1298 ∨ p1303)
    (h7827 : p1299 ∨ p1303)
    (h7832 : p1300 ∨ p1303)
    (h7730 : p1291 ∨ p1292 ∨ (¬ p1296) ∨ (¬ p1297) ∨ (¬ p1298) ∨ (¬ p1299) ∨ (¬ p1300)) : p1291 ∨ p1292 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1291) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1292) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p1303) := by
    rcases h24794 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1296 := by
    rcases h7812 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : p1297 := by
    rcases h7817 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p1298 := by
    rcases h7822 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p1299 := by
    rcases h7827 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p1300 := by
    rcases h7832 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h7730 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24796 (p1159 p1167 p1175 p1176 p1177 p1178 p1179 p1180 : Prop)
    (h7014 : p1175 ∨ p1176)
    (h7015 : p1175 ∨ p1177)
    (h7016 : p1175 ∨ p1178)
    (h7018 : p1175 ∨ p1180)
    (h6929 : p1159 ∨ p1167 ∨ (¬ p1176) ∨ (¬ p1177) ∨ (¬ p1178) ∨ (¬ p1179) ∨ (¬ p1180)) : p1175 ∨ (¬ p1179) ∨ p1167 ∨ p1159 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1175) := fun hu => hn (Or.inl hu)
  have u1 : p1179 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1167) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1159) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1176 := by
    rcases h7014 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1177 := by
    rcases h7015 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1178 := by
    rcases h7016 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1180 := by
    rcases h7018 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6929 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step24802 (p3 p12 p15 p18 p19 p39 p41 p45 p46 p48 p63 p69 p70 p85 p102 p103 p121 p126 p136 p140 p189 p228 p256 p258 p288 p301 p303 p323 p345 p350 p387 p519 p616 p665 p789 p790 p858 p1036 p1077 p1226 p1237 p1333 p1385 : Prop)
    (h12629 : (¬ p126) ∨ (¬ p301))
    (h24776 : p519 ∨ p301)
    (h10565 : (¬ p256) ∨ (¬ p519) ∨ p790)
    (h16678 : (¬ p126) ∨ (¬ p256) ∨ (¬ p387) ∨ (¬ p1333))
    (h19251 : (¬ p41) ∨ (¬ p126) ∨ (¬ p189) ∨ (¬ p256))
    (h5964 : (¬ p136) ∨ (¬ p189) ∨ (¬ p256))
    (h18095 : (¬ p189) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p1077))
    (h21214 : p228 ∨ p387)
    (h21394 : p387 ∨ p303)
    (h21444 : p41 ∨ p45)
    (h22195 : p46 ∨ p41)
    (h22080 : p136 ∨ p140)
    (h21668 : p258 ∨ p288)
    (h15063 : (¬ p102) ∨ (¬ p140) ∨ p288)
    (h18640 : (¬ p189) ∨ (¬ p303) ∨ (¬ p789) ∨ (¬ p790))
    (h20575 : (¬ p18) ∨ (¬ p46) ∨ (¬ p140) ∨ (¬ p189) ∨ (¬ p256))
    (h9410 : (¬ p126) ∨ (¬ p258) ∨ (¬ p345))
    (h21873 : p103 ∨ p102)
    (h22497 : p858 ∨ p789)
    (h22840 : p19 ∨ p18)
    (h21667 : p350 ∨ p345)
    (h18777 : (¬ p103) ∨ (¬ p323) ∨ (¬ p350) ∨ (¬ p1036) ∨ (¬ p1077))
    (h18674 : (¬ p15) ∨ (¬ p19) ∨ (¬ p121) ∨ (¬ p228) ∨ (¬ p1226) ∨ (¬ p1237) ∨ (¬ p1333))
    (h22941 : p1036 ∨ p12)
    (h21946 : p69 ∨ p15)
    (h24699 : p70 ∨ p15)
    (h24703 : p1385 ∨ (¬ p45) ∨ (¬ p69) ∨ p616)
    (h16878 : (¬ p3) ∨ (¬ p12) ∨ (¬ p70) ∨ (¬ p85) ∨ (¬ p665) ∨ (¬ p858) ∨ (¬ p1385))
    (h24705 : (¬ p790) ∨ (¬ p39) ∨ (¬ p1385) ∨ (¬ p69))
    (h22211 : p85 ∨ p63)
    (h24704 : p39 ∨ p48 ∨ p41)
    (h11773 : (¬ p48) ∨ (¬ p63) ∨ (¬ p69)) : (¬ p256) ∨ (¬ p126) ∨ p616 ∨ (¬ p1237) ∨ (¬ p121) ∨ (¬ p1077) ∨ (¬ p665) ∨ (¬ p323) ∨ (¬ p3) ∨ (¬ p189) ∨ (¬ p1226) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p616) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))
  have u12 : (¬ p301) := by
    rcases h12629 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  have u13 : p519 := by
    rcases h24776 with q0 | q1
    · exact q0
    · exact False.elim (u12 q1)
  have u14 : p790 := by
    rcases h10565 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact False.elim (q1 u13)
    · exact q2
  have u15 : (¬ p387) := by
    rcases h16678 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u1)
    · exact False.elim (q1 u0)
    · exact q2
    · exact False.elim (q3 u11)
  have u16 : (¬ p41) := by
    rcases h19251 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u1)
    · exact False.elim (q2 u9)
    · exact False.elim (q3 u0)
  have u17 : (¬ p136) := by
    rcases h5964 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u9)
    · exact False.elim (q2 u0)
  have u18 : (¬ p288) := by
    rcases h18095 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u9)
    · exact False.elim (q1 u0)
    · exact q2
    · exact False.elim (q3 u5)
  have u19 : p228 := by
    rcases h21214 with q0 | q1
    · exact q0
    · exact False.elim (u15 q1)
  have u20 : p303 := by
    rcases h21394 with q0 | q1
    · exact False.elim (u15 q0)
    · exact q1
  have u21 : p45 := by
    rcases h21444 with q0 | q1
    · exact False.elim (u16 q0)
    · exact q1
  have u22 : p46 := by
    rcases h22195 with q0 | q1
    · exact q0
    · exact False.elim (u16 q1)
  have u23 : p140 := by
    rcases h22080 with q0 | q1
    · exact False.elim (u17 q0)
    · exact q1
  have u24 : p258 := by
    rcases h21668 with q0 | q1
    · exact q0
    · exact False.elim (u18 q1)
  have u25 : (¬ p102) := by
    rcases h15063 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u23)
    · exact False.elim (u18 q2)
  have u26 : (¬ p789) := by
    rcases h18640 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u9)
    · exact False.elim (q1 u20)
    · exact q2
    · exact False.elim (q3 u14)
  have u27 : (¬ p18) := by
    rcases h20575 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u22)
    · exact False.elim (q2 u23)
    · exact False.elim (q3 u9)
    · exact False.elim (q4 u0)
  have u28 : (¬ p345) := by
    rcases h9410 with q0 | q1 | q2
    · exact False.elim (q0 u1)
    · exact False.elim (q1 u24)
    · exact q2
  have u29 : p103 := by
    rcases h21873 with q0 | q1
    · exact q0
    · exact False.elim (u25 q1)
  have u30 : p858 := by
    rcases h22497 with q0 | q1
    · exact q0
    · exact False.elim (u26 q1)
  have u31 : p19 := by
    rcases h22840 with q0 | q1
    · exact q0
    · exact False.elim (u27 q1)
  have u32 : p350 := by
    rcases h21667 with q0 | q1
    · exact q0
    · exact False.elim (u28 q1)
  have u33 : (¬ p1036) := by
    rcases h18777 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u29)
    · exact False.elim (q1 u7)
    · exact False.elim (q2 u32)
    · exact q3
    · exact False.elim (q4 u5)
  have u34 : (¬ p15) := by
    rcases h18674 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact q0
    · exact False.elim (q1 u31)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u19)
    · exact False.elim (q4 u10)
    · exact False.elim (q5 u3)
    · exact False.elim (q6 u11)
  have u35 : p12 := by
    rcases h22941 with q0 | q1
    · exact False.elim (u33 q0)
    · exact q1
  have u36 : p69 := by
    rcases h21946 with q0 | q1
    · exact q0
    · exact False.elim (u34 q1)
  have u37 : p70 := by
    rcases h24699 with q0 | q1
    · exact q0
    · exact False.elim (u34 q1)
  have u38 : p1385 := by
    rcases h24703 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u21)
    · exact False.elim (q2 u36)
    · exact False.elim (u2 q3)
  have u39 : (¬ p85) := by
    rcases h16878 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u8)
    · exact False.elim (q1 u35)
    · exact False.elim (q2 u37)
    · exact q3
    · exact False.elim (q4 u6)
    · exact False.elim (q5 u30)
    · exact False.elim (q6 u38)
  have u40 : (¬ p39) := by
    rcases h24705 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u14)
    · exact q1
    · exact False.elim (q2 u38)
    · exact False.elim (q3 u36)
  have u41 : p63 := by
    rcases h22211 with q0 | q1
    · exact False.elim (u39 q0)
    · exact q1
  have u42 : p48 := by
    rcases h24704 with q0 | q1 | q2
    · exact False.elim (u40 q0)
    · exact q1
    · exact False.elim (u16 q2)
  rcases h11773 with q0 | q1 | q2
  · exact False.elim (q0 u42)
  · exact False.elim (q1 u41)
  · exact False.elim (q2 u36)

theorem step24803 (p3 p12 p15 p39 p41 p44 p45 p48 p63 p69 p70 p85 p167 p187 p188 p193 p237 p616 p665 p790 p814 p858 p918 p928 p1385 : Prop)
    (h23818 : p41 ∨ p44)
    (h21444 : p41 ∨ p45)
    (h23862 : p188 ∨ p193)
    (h22383 : (¬ p188) ∨ p193 ∨ p3 ∨ (¬ p237))
    (h24369 : p187 ∨ p193)
    (h5458 : (¬ p3) ∨ (¬ p167) ∨ (¬ p187))
    (h21946 : p69 ∨ p15)
    (h24699 : p70 ∨ p15)
    (h24703 : p1385 ∨ (¬ p45) ∨ (¬ p69) ∨ p616)
    (h16878 : (¬ p3) ∨ (¬ p12) ∨ (¬ p70) ∨ (¬ p85) ∨ (¬ p665) ∨ (¬ p858) ∨ (¬ p1385))
    (h22211 : p85 ∨ p63)
    (h11773 : (¬ p48) ∨ (¬ p63) ∨ (¬ p69))
    (h23944 : (¬ p928) ∨ p167 ∨ (¬ p69) ∨ (¬ p44) ∨ (¬ p45) ∨ (¬ p63))
    (h24704 : p39 ∨ p48 ∨ p41)
    (h22025 : p918 ∨ p928)
    (h24705 : (¬ p790) ∨ (¬ p39) ∨ (¬ p1385) ∨ (¬ p69))
    (h20331 : (¬ p237) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p918))
    (h20735 : p790 ∨ p814) : p15 ∨ (¬ p858) ∨ (¬ p12) ∨ p41 ∨ p616 ∨ (¬ p665) ∨ p193 ∨ (¬ p237) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p15) := fun hu => hn (Or.inl hu)
  have u1 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p616) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p193) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p44 := by
    rcases h23818 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  have u9 : p45 := by
    rcases h21444 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  have u10 : p188 := by
    rcases h23862 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p3 := by
    rcases h22383 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u10)
    · exact False.elim (u6 q1)
    · exact q2
    · exact False.elim (q3 u7)
  have u12 : p187 := by
    rcases h24369 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u13 : (¬ p167) := by
    rcases h5458 with q0 | q1 | q2
    · exact False.elim (q0 u11)
    · exact q1
    · exact False.elim (q2 u12)
  have u14 : p69 := by
    rcases h21946 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u15 : p70 := by
    rcases h24699 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u16 : p1385 := by
    rcases h24703 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u9)
    · exact False.elim (q2 u14)
    · exact False.elim (u4 q3)
  have u17 : (¬ p85) := by
    rcases h16878 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u11)
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u15)
    · exact q3
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u1)
    · exact False.elim (q6 u16)
  have u18 : p63 := by
    rcases h22211 with q0 | q1
    · exact False.elim (u17 q0)
    · exact q1
  have u19 : (¬ p48) := by
    rcases h11773 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u18)
    · exact False.elim (q2 u14)
  have u20 : (¬ p928) := by
    rcases h23944 with q0 | q1 | q2 | q3 | q4 | q5
    · exact q0
    · exact False.elim (u13 q1)
    · exact False.elim (q2 u14)
    · exact False.elim (q3 u8)
    · exact False.elim (q4 u9)
    · exact False.elim (q5 u18)
  have u21 : p39 := by
    rcases h24704 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u19 q1)
    · exact False.elim (u3 q2)
  have u22 : p918 := by
    rcases h22025 with q0 | q1
    · exact q0
    · exact False.elim (u20 q1)
  have u23 : (¬ p790) := by
    rcases h24705 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u21)
    · exact False.elim (q2 u16)
    · exact False.elim (q3 u14)
  have u24 : (¬ p814) := by
    rcases h20331 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u7)
    · exact q1
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u22)
  rcases h20735 with q0 | q1
  · exact False.elim (u23 q0)
  · exact False.elim (u24 q1)

theorem step24806 (p10 p12 p101 p102 p103 p107 p323 p345 p350 p1036 p1077 : Prop)
    (h1698 : (¬ p10) ∨ (¬ p323))
    (h22941 : p1036 ∨ p12)
    (h13032 : p12 ∨ (¬ p107) ∨ (¬ p1077))
    (h24548 : p107 ∨ p101)
    (h519 : (¬ p101) ∨ (¬ p102))
    (h14198 : p10 ∨ (¬ p101) ∨ (¬ p345))
    (h21873 : p103 ∨ p102)
    (h21667 : p350 ∨ p345)
    (h18777 : (¬ p103) ∨ (¬ p323) ∨ (¬ p350) ∨ (¬ p1036) ∨ (¬ p1077)) : p12 ∨ (¬ p1077) ∨ (¬ p323) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p12) := fun hu => hn (Or.inl hu)
  have u1 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p10) := by
    rcases h1698 with q0 | q1
    · exact q0
    · exact False.elim (q1 u2)
  have u4 : p1036 := by
    rcases h22941 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : (¬ p107) := by
    rcases h13032 with q0 | q1 | q2
    · exact False.elim (u0 q0)
    · exact q1
    · exact False.elim (q2 u1)
  have u6 : p101 := by
    rcases h24548 with q0 | q1
    · exact False.elim (u5 q0)
    · exact q1
  have u7 : (¬ p102) := by
    rcases h519 with q0 | q1
    · exact False.elim (q0 u6)
    · exact q1
  have u8 : (¬ p345) := by
    rcases h14198 with q0 | q1 | q2
    · exact False.elim (u3 q0)
    · exact False.elim (q1 u6)
    · exact q2
  have u9 : p103 := by
    rcases h21873 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p350 := by
    rcases h21667 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h18777 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u1)

theorem step24808 (p17 p101 p134 p137 p143 p237 p258 p283 p286 p288 : Prop)
    (h8758 : (¬ p17) ∨ (¬ p237) ∨ (¬ p283))
    (h21864 : p283 ∨ p288)
    (h9406 : (¬ p258) ∨ (¬ p288))
    (h12323 : (¬ p101) ∨ (¬ p137) ∨ (¬ p288))
    (h21140 : p286 ∨ p258)
    (h24289 : p143 ∨ p134 ∨ p137)
    (h16875 : (¬ p17) ∨ (¬ p101) ∨ (¬ p143) ∨ (¬ p237) ∨ (¬ p286)) : (¬ p17) ∨ p134 ∨ (¬ p237) ∨ (¬ p101) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p134) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p283) := by
    rcases h8758 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact False.elim (q1 u2)
    · exact q2
  have u5 : p288 := by
    rcases h21864 with q0 | q1
    · exact False.elim (u4 q0)
    · exact q1
  have u6 : (¬ p258) := by
    rcases h9406 with q0 | q1
    · exact q0
    · exact False.elim (q1 u5)
  have u7 : (¬ p137) := by
    rcases h12323 with q0 | q1 | q2
    · exact False.elim (q0 u3)
    · exact q1
    · exact False.elim (q2 u5)
  have u8 : p286 := by
    rcases h21140 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p143 := by
    rcases h24289 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u7 q2)
  rcases h16875 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u8)

theorem step24810 (p1252 p1257 p1259 p1260 p1261 p1262 p1263 p1267 : Prop)
    (h7560 : p1259 ∨ p1267)
    (h7565 : p1260 ∨ p1267)
    (h7570 : p1261 ∨ p1267)
    (h7575 : p1262 ∨ p1267)
    (h7580 : p1263 ∨ p1267)
    (h7460 : p1252 ∨ p1257 ∨ (¬ p1259) ∨ (¬ p1260) ∨ (¬ p1261) ∨ (¬ p1262) ∨ (¬ p1263)) : p1267 ∨ p1257 ∨ p1252 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1267) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1257) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1252) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1259 := by
    rcases h7560 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1260 := by
    rcases h7565 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1261 := by
    rcases h7570 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1262 := by
    rcases h7575 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1263 := by
    rcases h7580 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7460 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step24811 (p1252 p1257 p1259 p1264 p1265 p1266 p1267 p1268 : Prop)
    (h24810 : p1267 ∨ p1257 ∨ p1252)
    (h7557 : p1259 ∨ p1264)
    (h7558 : p1259 ∨ p1265)
    (h7559 : p1259 ∨ p1266)
    (h7561 : p1259 ∨ p1268)
    (h7485 : p1252 ∨ p1257 ∨ (¬ p1264) ∨ (¬ p1265) ∨ (¬ p1266) ∨ (¬ p1267) ∨ (¬ p1268)) : p1259 ∨ p1257 ∨ p1252 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1259) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1257) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1252) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1267 := by
    rcases h24810 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1264 := by
    rcases h7557 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1265 := by
    rcases h7558 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1266 := by
    rcases h7559 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1268 := by
    rcases h7561 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7485 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24812 (p1252 p1257 p1260 p1264 p1265 p1266 p1267 p1268 : Prop)
    (h24810 : p1267 ∨ p1257 ∨ p1252)
    (h7562 : p1260 ∨ p1264)
    (h7563 : p1260 ∨ p1265)
    (h7564 : p1260 ∨ p1266)
    (h7566 : p1260 ∨ p1268)
    (h7485 : p1252 ∨ p1257 ∨ (¬ p1264) ∨ (¬ p1265) ∨ (¬ p1266) ∨ (¬ p1267) ∨ (¬ p1268)) : p1260 ∨ p1257 ∨ p1252 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1260) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1257) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1252) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1267 := by
    rcases h24810 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1264 := by
    rcases h7562 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1265 := by
    rcases h7563 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1266 := by
    rcases h7564 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1268 := by
    rcases h7566 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7485 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24813 (p1252 p1257 p1261 p1264 p1265 p1266 p1267 p1268 : Prop)
    (h24810 : p1267 ∨ p1257 ∨ p1252)
    (h7567 : p1261 ∨ p1264)
    (h7568 : p1261 ∨ p1265)
    (h7569 : p1261 ∨ p1266)
    (h7571 : p1261 ∨ p1268)
    (h7485 : p1252 ∨ p1257 ∨ (¬ p1264) ∨ (¬ p1265) ∨ (¬ p1266) ∨ (¬ p1267) ∨ (¬ p1268)) : p1261 ∨ p1257 ∨ p1252 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1261) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1257) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1252) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1267 := by
    rcases h24810 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1264 := by
    rcases h7567 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1265 := by
    rcases h7568 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1266 := by
    rcases h7569 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1268 := by
    rcases h7571 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7485 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24814 (p1252 p1257 p1262 p1264 p1265 p1266 p1267 p1268 : Prop)
    (h24810 : p1267 ∨ p1257 ∨ p1252)
    (h7572 : p1262 ∨ p1264)
    (h7573 : p1262 ∨ p1265)
    (h7574 : p1262 ∨ p1266)
    (h7576 : p1262 ∨ p1268)
    (h7485 : p1252 ∨ p1257 ∨ (¬ p1264) ∨ (¬ p1265) ∨ (¬ p1266) ∨ (¬ p1267) ∨ (¬ p1268)) : p1262 ∨ p1257 ∨ p1252 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1262) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1257) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1252) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1267 := by
    rcases h24810 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1264 := by
    rcases h7572 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1265 := by
    rcases h7573 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1266 := by
    rcases h7574 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1268 := by
    rcases h7576 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7485 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step24815 (p3 p12 p13 p15 p17 p27 p41 p45 p46 p70 p84 p85 p101 p126 p161 p165 p169 p188 p189 p193 p224 p237 p256 p265 p304 p362 p384 p387 p422 p424 p455 p456 p495 p499 p532 p576 p580 p595 p600 p616 p633 p636 p657 p840 p918 p927 p928 p980 p983 p1035 p1036 p1042 p1084 p1096 p1099 p1140 p1225 p1227 p1249 p1252 p1257 p1259 p1260 p1261 p1262 p1263 p1264 p1265 p1266 p1267 p1268 p1269 p1325 p1333 p1452 p1465 p1489 p1508 : Prop)
    (h9340 : (¬ p12) ∨ (¬ p1036))
    (h23109 : p1042 ∨ p1036)
    (h21454 : p237 ∨ (¬ p256) ∨ (¬ p126))
    (h6740 : (¬ p189) ∨ (¬ p193))
    (h23862 : p188 ∨ p193)
    (h22383 : (¬ p188) ∨ p193 ∨ p3 ∨ (¬ p237))
    (h13487 : (¬ p3) ∨ (¬ p1042) ∨ p1140)
    (h19251 : (¬ p41) ∨ (¬ p126) ∨ (¬ p189) ∨ (¬ p256))
    (h22195 : p46 ∨ p41)
    (h21444 : p41 ∨ p45)
    (h6736 : (¬ p165) ∨ (¬ p189) ∨ (¬ p237))
    (h21921 : p165 ∨ p169)
    (h21572 : p161 ∨ p1225)
    (h10652 : (¬ p17) ∨ (¬ p256))
    (h21151 : p17 ∨ p265)
    (h11184 : (¬ p126) ∨ (¬ p265) ∨ p362)
    (h10651 : (¬ p595) ∨ (¬ p616))
    (h10781 : (¬ p499) ∨ (¬ p600) ∨ (¬ p616))
    (h10283 : p495 ∨ (¬ p600) ∨ (¬ p616))
    (h23930 : p595 ∨ (¬ p15) ∨ (¬ p424) ∨ (¬ p46))
    (h24379 : (¬ p1096) ∨ p499 ∨ (¬ p27) ∨ (¬ p101))
    (h22399 : p84 ∨ (¬ p495) ∨ p17)
    (h24699 : p70 ∨ p15)
    (h21802 : p1096 ∨ p1099)
    (h8726 : (¬ p84) ∨ (¬ p237) ∨ (¬ p918))
    (h19253 : (¬ p12) ∨ (¬ p45) ∨ (¬ p84) ∨ (¬ p169) ∨ (¬ p237) ∨ (¬ p983))
    (h10747 : (¬ p84) ∨ (¬ p256) ∨ (¬ p576))
    (h22025 : p918 ∨ p928)
    (h23359 : p927 ∨ p918)
    (h20687 : p980 ∨ p983)
    (h21165 : p576 ∨ p580)
    (h16252 : (¬ p45) ∨ (¬ p657) ∨ (¬ p840) ∨ (¬ p928))
    (h12049 : p85 ∨ (¬ p927) ∨ (¬ p1099))
    (h17397 : (¬ p45) ∨ (¬ p304) ∨ (¬ p362) ∨ (¬ p580) ∨ (¬ p633))
    (h20814 : p224 ∨ p657)
    (h21879 : p636 ∨ p633)
    (h18102 : (¬ p126) ∨ (¬ p224) ∨ (¬ p256) ∨ (¬ p387))
    (h21972 : (¬ p1225) ∨ (¬ p532) ∨ (¬ p1084) ∨ (¬ p636))
    (h24334 : p384 ∨ p387)
    (h21329 : p1452 ∨ p532)
    (h19248 : (¬ p455) ∨ (¬ p636) ∨ (¬ p980) ∨ (¬ p1452))
    (h11192 : (¬ p384) ∨ (¬ p1325) ∨ (¬ p1452))
    (h20925 : p455 ∨ p456)
    (h21656 : p1325 ∨ p1333)
    (h19249 : (¬ p13) ∨ (¬ p70) ∨ (¬ p456) ∨ (¬ p495) ∨ (¬ p980) ∨ (¬ p1035) ∨ (¬ p1140))
    (h21566 : p1465 ∨ p1035)
    (h24787 : (¬ p1508) ∨ (¬ p189) ∨ (¬ p237) ∨ (¬ p1465) ∨ (¬ p980))
    (h21548 : p1508 ∨ p1489)
    (h16847 : (¬ p85) ∨ (¬ p1249) ∨ (¬ p1333) ∨ (¬ p1489))
    (h12910 : p161 ∨ (¬ p1269) ∨ (¬ p1489))
    (h12370 : (¬ p45) ∨ p1249 ∨ (¬ p1252))
    (h22891 : p1227 ∨ p1269)
    (h17399 : (¬ p45) ∨ (¬ p1225) ∨ (¬ p1227) ∨ (¬ p1257) ∨ (¬ p1489))
    (h24810 : p1267 ∨ p1257 ∨ p1252)
    (h24811 : p1259 ∨ p1257 ∨ p1252)
    (h24812 : p1260 ∨ p1257 ∨ p1252)
    (h24813 : p1261 ∨ p1257 ∨ p1252)
    (h24814 : p1262 ∨ p1257 ∨ p1252)
    (h7470 : p422 ∨ p1257 ∨ (¬ p1259) ∨ (¬ p1260) ∨ (¬ p1261) ∨ (¬ p1262) ∨ (¬ p1263))
    (h7577 : p1263 ∨ p1264)
    (h7578 : p1263 ∨ p1265)
    (h7579 : p1263 ∨ p1266)
    (h7581 : p1263 ∨ p1268)
    (h7485 : p1252 ∨ p1257 ∨ (¬ p1264) ∨ (¬ p1265) ∨ (¬ p1266) ∨ (¬ p1267) ∨ (¬ p1268)) : (¬ p616) ∨ (¬ p840) ∨ (¬ p600) ∨ (¬ p27) ∨ (¬ p304) ∨ (¬ p101) ∨ p422 ∨ (¬ p189) ∨ p161 ∨ (¬ p1084) ∨ (¬ p13) ∨ (¬ p12) ∨ (¬ p424) ∨ (¬ p126) ∨ (¬ p256) := by
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
  have u2 : p600 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p27 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p161) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))))))
  have u15 : (¬ p1036) := by
    rcases h9340 with q0 | q1
    · exact False.elim (q0 u11)
    · exact q1
  have u16 : p1042 := by
    rcases h23109 with q0 | q1
    · exact q0
    · exact False.elim (u15 q1)
  have u17 : p237 := by
    rcases h21454 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u14)
    · exact False.elim (q2 u13)
  have u18 : (¬ p193) := by
    rcases h6740 with q0 | q1
    · exact False.elim (q0 u7)
    · exact q1
  have u19 : p188 := by
    rcases h23862 with q0 | q1
    · exact q0
    · exact False.elim (u18 q1)
  have u20 : p3 := by
    rcases h22383 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u19)
    · exact False.elim (u18 q1)
    · exact q2
    · exact False.elim (q3 u17)
  have u21 : p1140 := by
    rcases h13487 with q0 | q1 | q2
    · exact False.elim (q0 u20)
    · exact False.elim (q1 u16)
    · exact q2
  have u22 : (¬ p41) := by
    rcases h19251 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u13)
    · exact False.elim (q2 u7)
    · exact False.elim (q3 u14)
  have u23 : p46 := by
    rcases h22195 with q0 | q1
    · exact q0
    · exact False.elim (u22 q1)
  have u24 : p45 := by
    rcases h21444 with q0 | q1
    · exact False.elim (u22 q0)
    · exact q1
  have u25 : (¬ p165) := by
    rcases h6736 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u7)
    · exact False.elim (q2 u17)
  have u26 : p169 := by
    rcases h21921 with q0 | q1
    · exact False.elim (u25 q0)
    · exact q1
  have u27 : p1225 := by
    rcases h21572 with q0 | q1
    · exact False.elim (u8 q0)
    · exact q1
  have u28 : (¬ p17) := by
    rcases h10652 with q0 | q1
    · exact q0
    · exact False.elim (q1 u14)
  have u29 : p265 := by
    rcases h21151 with q0 | q1
    · exact False.elim (u28 q0)
    · exact q1
  have u30 : p362 := by
    rcases h11184 with q0 | q1 | q2
    · exact False.elim (q0 u13)
    · exact False.elim (q1 u29)
    · exact q2
  have u31 : (¬ p595) := by
    rcases h10651 with q0 | q1
    · exact q0
    · exact False.elim (q1 u0)
  have u32 : (¬ p499) := by
    rcases h10781 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u0)
  have u33 : p495 := by
    rcases h10283 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u0)
  have u34 : (¬ p15) := by
    rcases h23930 with q0 | q1 | q2 | q3
    · exact False.elim (u31 q0)
    · exact q1
    · exact False.elim (q2 u12)
    · exact False.elim (q3 u23)
  have u35 : (¬ p1096) := by
    rcases h24379 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (u32 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u5)
  have u36 : p84 := by
    rcases h22399 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u33)
    · exact False.elim (u28 q2)
  have u37 : p70 := by
    rcases h24699 with q0 | q1
    · exact q0
    · exact False.elim (u34 q1)
  have u38 : p1099 := by
    rcases h21802 with q0 | q1
    · exact False.elim (u35 q0)
    · exact q1
  have u39 : (¬ p918) := by
    rcases h8726 with q0 | q1 | q2
    · exact False.elim (q0 u36)
    · exact False.elim (q1 u17)
    · exact q2
  have u40 : (¬ p983) := by
    rcases h19253 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u11)
    · exact False.elim (q1 u24)
    · exact False.elim (q2 u36)
    · exact False.elim (q3 u26)
    · exact False.elim (q4 u17)
    · exact q5
  have u41 : (¬ p576) := by
    rcases h10747 with q0 | q1 | q2
    · exact False.elim (q0 u36)
    · exact False.elim (q1 u14)
    · exact q2
  have u42 : p928 := by
    rcases h22025 with q0 | q1
    · exact False.elim (u39 q0)
    · exact q1
  have u43 : p927 := by
    rcases h23359 with q0 | q1
    · exact q0
    · exact False.elim (u39 q1)
  have u44 : p980 := by
    rcases h20687 with q0 | q1
    · exact q0
    · exact False.elim (u40 q1)
  have u45 : p580 := by
    rcases h21165 with q0 | q1
    · exact False.elim (u41 q0)
    · exact q1
  have u46 : (¬ p657) := by
    rcases h16252 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u24)
    · exact q1
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u42)
  have u47 : p85 := by
    rcases h12049 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u43)
    · exact False.elim (q2 u38)
  have u48 : (¬ p633) := by
    rcases h17397 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u24)
    · exact False.elim (q1 u4)
    · exact False.elim (q2 u30)
    · exact False.elim (q3 u45)
    · exact q4
  have u49 : p224 := by
    rcases h20814 with q0 | q1
    · exact q0
    · exact False.elim (u46 q1)
  have u50 : p636 := by
    rcases h21879 with q0 | q1
    · exact q0
    · exact False.elim (u48 q1)
  have u51 : (¬ p387) := by
    rcases h18102 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u13)
    · exact False.elim (q1 u49)
    · exact False.elim (q2 u14)
    · exact q3
  have u52 : (¬ p532) := by
    rcases h21972 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u27)
    · exact q1
    · exact False.elim (q2 u9)
    · exact False.elim (q3 u50)
  have u53 : p384 := by
    rcases h24334 with q0 | q1
    · exact q0
    · exact False.elim (u51 q1)
  have u54 : p1452 := by
    rcases h21329 with q0 | q1
    · exact q0
    · exact False.elim (u52 q1)
  have u55 : (¬ p455) := by
    rcases h19248 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u50)
    · exact False.elim (q2 u44)
    · exact False.elim (q3 u54)
  have u56 : (¬ p1325) := by
    rcases h11192 with q0 | q1 | q2
    · exact False.elim (q0 u53)
    · exact q1
    · exact False.elim (q2 u54)
  have u57 : p456 := by
    rcases h20925 with q0 | q1
    · exact False.elim (u55 q0)
    · exact q1
  have u58 : p1333 := by
    rcases h21656 with q0 | q1
    · exact False.elim (u56 q0)
    · exact q1
  have u59 : (¬ p1035) := by
    rcases h19249 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u10)
    · exact False.elim (q1 u37)
    · exact False.elim (q2 u57)
    · exact False.elim (q3 u33)
    · exact False.elim (q4 u44)
    · exact q5
    · exact False.elim (q6 u21)
  have u60 : p1465 := by
    rcases h21566 with q0 | q1
    · exact q0
    · exact False.elim (u59 q1)
  have u61 : (¬ p1508) := by
    rcases h24787 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u7)
    · exact False.elim (q2 u17)
    · exact False.elim (q3 u60)
    · exact False.elim (q4 u44)
  have u62 : p1489 := by
    rcases h21548 with q0 | q1
    · exact False.elim (u61 q0)
    · exact q1
  have u63 : (¬ p1249) := by
    rcases h16847 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u47)
    · exact q1
    · exact False.elim (q2 u58)
    · exact False.elim (q3 u62)
  have u64 : (¬ p1269) := by
    rcases h12910 with q0 | q1 | q2
    · exact False.elim (u8 q0)
    · exact q1
    · exact False.elim (q2 u62)
  have u65 : (¬ p1252) := by
    rcases h12370 with q0 | q1 | q2
    · exact False.elim (q0 u24)
    · exact False.elim (u63 q1)
    · exact q2
  have u66 : p1227 := by
    rcases h22891 with q0 | q1
    · exact q0
    · exact False.elim (u64 q1)
  have u67 : (¬ p1257) := by
    rcases h17399 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u24)
    · exact False.elim (q1 u27)
    · exact False.elim (q2 u66)
    · exact q3
    · exact False.elim (q4 u62)
  have u68 : p1267 := by
    rcases h24810 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u67 q1)
    · exact False.elim (u65 q2)
  have u69 : p1259 := by
    rcases h24811 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u67 q1)
    · exact False.elim (u65 q2)
  have u70 : p1260 := by
    rcases h24812 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u67 q1)
    · exact False.elim (u65 q2)
  have u71 : p1261 := by
    rcases h24813 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u67 q1)
    · exact False.elim (u65 q2)
  have u72 : p1262 := by
    rcases h24814 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u67 q1)
    · exact False.elim (u65 q2)
  have u73 : (¬ p1263) := by
    rcases h7470 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u6 q0)
    · exact False.elim (u67 q1)
    · exact False.elim (q2 u69)
    · exact False.elim (q3 u70)
    · exact False.elim (q4 u71)
    · exact False.elim (q5 u72)
    · exact q6
  have u74 : p1264 := by
    rcases h7577 with q0 | q1
    · exact False.elim (u73 q0)
    · exact q1
  have u75 : p1265 := by
    rcases h7578 with q0 | q1
    · exact False.elim (u73 q0)
    · exact q1
  have u76 : p1266 := by
    rcases h7579 with q0 | q1
    · exact False.elim (u73 q0)
    · exact q1
  have u77 : p1268 := by
    rcases h7581 with q0 | q1
    · exact False.elim (u73 q0)
    · exact q1
  rcases h7485 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u65 q0)
  · exact False.elim (u67 q1)
  · exact False.elim (q2 u74)
  · exact False.elim (q3 u75)
  · exact False.elim (q4 u76)
  · exact False.elim (q5 u68)
  · exact False.elim (q6 u77)

theorem step24816 (p1252 p1257 p1259 p1260 p1261 p1262 p1263 p1264 p1265 p1266 p1267 p1268 : Prop)
    (h24810 : p1267 ∨ p1257 ∨ p1252)
    (h24811 : p1259 ∨ p1257 ∨ p1252)
    (h24812 : p1260 ∨ p1257 ∨ p1252)
    (h24813 : p1261 ∨ p1257 ∨ p1252)
    (h24814 : p1262 ∨ p1257 ∨ p1252)
    (h7460 : p1252 ∨ p1257 ∨ (¬ p1259) ∨ (¬ p1260) ∨ (¬ p1261) ∨ (¬ p1262) ∨ (¬ p1263))
    (h7577 : p1263 ∨ p1264)
    (h7578 : p1263 ∨ p1265)
    (h7579 : p1263 ∨ p1266)
    (h7581 : p1263 ∨ p1268)
    (h7485 : p1252 ∨ p1257 ∨ (¬ p1264) ∨ (¬ p1265) ∨ (¬ p1266) ∨ (¬ p1267) ∨ (¬ p1268)) : p1257 ∨ p1252 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1257) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1252) := fun hu => hn (Or.inr hu)
  have u2 : p1267 := by
    rcases h24810 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1259 := by
    rcases h24811 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1260 := by
    rcases h24812 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1261 := by
    rcases h24813 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p1262 := by
    rcases h24814 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p1263) := by
    rcases h7460 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p1264 := by
    rcases h7577 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p1265 := by
    rcases h7578 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p1266 := by
    rcases h7579 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p1268 := by
    rcases h7581 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h7485 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u11)

theorem step24817 (p45 p161 p1225 p1227 p1252 p1257 p1269 p1273 p1489 : Prop)
    (h11740 : (¬ p161) ∨ (¬ p1225))
    (h12910 : p161 ∨ (¬ p1269) ∨ (¬ p1489))
    (h20866 : p1273 ∨ p1269)
    (h22891 : p1227 ∨ p1269)
    (h12368 : (¬ p45) ∨ (¬ p1252) ∨ (¬ p1273))
    (h17399 : (¬ p45) ∨ (¬ p1225) ∨ (¬ p1227) ∨ (¬ p1257) ∨ (¬ p1489))
    (h24816 : p1257 ∨ p1252) : (¬ p1489) ∨ (¬ p1225) ∨ (¬ p45) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p161) := by
    rcases h11740 with q0 | q1
    · exact q0
    · exact False.elim (q1 u1)
  have u4 : (¬ p1269) := by
    rcases h12910 with q0 | q1 | q2
    · exact False.elim (u3 q0)
    · exact q1
    · exact False.elim (q2 u0)
  have u5 : p1273 := by
    rcases h20866 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u6 : p1227 := by
    rcases h22891 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u7 : (¬ p1252) := by
    rcases h12368 with q0 | q1 | q2
    · exact False.elim (q0 u2)
    · exact q1
    · exact False.elim (q2 u5)
  have u8 : (¬ p1257) := by
    rcases h17399 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u2)
    · exact False.elim (q1 u1)
    · exact False.elim (q2 u6)
    · exact q3
    · exact False.elim (q4 u0)
  rcases h24816 with q0 | q1
  · exact False.elim (u8 q0)
  · exact False.elim (u7 q1)

theorem step24823 (p165 p167 p171 p180 p182 : Prop)
    (h23752 : p182 ∨ p171 ∨ p167)
    (h23753 : p180 ∨ p171 ∨ p167)
    (h23773 : (¬ p182) ∨ (¬ p180) ∨ p165 ∨ p171) : p171 ∨ p167 ∨ p165 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p171) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p167) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p165) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p182 := by
    rcases h23752 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p180 := by
    rcases h23753 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h23773 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (u2 q2)
  · exact False.elim (u0 q3)

#print axioms step24823

end NineRUPTrial
