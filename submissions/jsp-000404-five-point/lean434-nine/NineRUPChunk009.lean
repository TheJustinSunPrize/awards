import Mathlib.Tactic.Tauto

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

namespace NineRUPTrial

theorem step21299 (p38 p67 p78 p79 p80 p81 : Prop)
    (h21294 : p78 ∨ p67 ∨ p38)
    (h21295 : p79 ∨ p67 ∨ p38)
    (h21296 : p80 ∨ p67 ∨ p38)
    (h21297 : p81 ∨ p67 ∨ p38)
    (h21298 : (¬ p81) ∨ (¬ p80) ∨ p38 ∨ p67 ∨ (¬ p78) ∨ (¬ p79)) : p67 ∨ p38 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p67) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p38) := fun hu => hn (Or.inr hu)
  have u2 : p78 := by
    rcases h21294 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p79 := by
    rcases h21295 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p80 := by
    rcases h21296 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p81 := by
    rcases h21297 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21298 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21300 (p477 p480 p484 p485 p486 p487 p488 p493 : Prop)
    (h2706 : p484 ∨ p493)
    (h2711 : p485 ∨ p493)
    (h2716 : p486 ∨ p493)
    (h2721 : p487 ∨ p493)
    (h2726 : p488 ∨ p493)
    (h2602 : p477 ∨ p480 ∨ (¬ p484) ∨ (¬ p485) ∨ (¬ p486) ∨ (¬ p487) ∨ (¬ p488)) : p493 ∨ p477 ∨ p480 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p493) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p477) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p480) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p484 := by
    rcases h2706 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p485 := by
    rcases h2711 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p486 := by
    rcases h2716 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p487 := by
    rcases h2721 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p488 := by
    rcases h2726 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2602 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21301 (p477 p480 p484 p485 p486 p487 p488 p489 : Prop)
    (h2702 : p484 ∨ p489)
    (h2707 : p485 ∨ p489)
    (h2712 : p486 ∨ p489)
    (h2717 : p487 ∨ p489)
    (h2722 : p488 ∨ p489)
    (h2602 : p477 ∨ p480 ∨ (¬ p484) ∨ (¬ p485) ∨ (¬ p486) ∨ (¬ p487) ∨ (¬ p488)) : p489 ∨ p477 ∨ p480 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p489) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p477) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p480) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p484 := by
    rcases h2702 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p485 := by
    rcases h2707 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p486 := by
    rcases h2712 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p487 := by
    rcases h2717 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p488 := by
    rcases h2722 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2602 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21302 (p477 p480 p484 p485 p486 p487 p488 p490 : Prop)
    (h2703 : p484 ∨ p490)
    (h2708 : p485 ∨ p490)
    (h2713 : p486 ∨ p490)
    (h2718 : p487 ∨ p490)
    (h2723 : p488 ∨ p490)
    (h2602 : p477 ∨ p480 ∨ (¬ p484) ∨ (¬ p485) ∨ (¬ p486) ∨ (¬ p487) ∨ (¬ p488)) : p490 ∨ p477 ∨ p480 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p490) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p477) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p480) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p484 := by
    rcases h2703 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p485 := by
    rcases h2708 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p486 := by
    rcases h2713 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p487 := by
    rcases h2718 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p488 := by
    rcases h2723 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2602 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21303 (p477 p480 p484 p485 p486 p487 p488 p491 : Prop)
    (h2704 : p484 ∨ p491)
    (h2709 : p485 ∨ p491)
    (h2714 : p486 ∨ p491)
    (h2719 : p487 ∨ p491)
    (h2724 : p488 ∨ p491)
    (h2602 : p477 ∨ p480 ∨ (¬ p484) ∨ (¬ p485) ∨ (¬ p486) ∨ (¬ p487) ∨ (¬ p488)) : p491 ∨ p477 ∨ p480 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p491) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p477) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p480) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h2602 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21304 (p477 p480 p484 p485 p486 p487 p488 p489 p490 p491 p492 p493 : Prop)
    (h2627 : p477 ∨ p480 ∨ (¬ p489) ∨ (¬ p490) ∨ (¬ p491) ∨ (¬ p492) ∨ (¬ p493))
    (h2705 : p484 ∨ p492)
    (h2710 : p485 ∨ p492)
    (h2715 : p486 ∨ p492)
    (h2720 : p487 ∨ p492)
    (h2725 : p488 ∨ p492)
    (h2602 : p477 ∨ p480 ∨ (¬ p484) ∨ (¬ p485) ∨ (¬ p486) ∨ (¬ p487) ∨ (¬ p488)) : (¬ p491) ∨ (¬ p489) ∨ p480 ∨ (¬ p493) ∨ p477 ∨ (¬ p490) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p491 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p480) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p493 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p477) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p490 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p492) := by
    rcases h2627 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u4 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u0)
    · exact q5
    · exact False.elim (q6 u3)
  have u7 : p484 := by
    rcases h2705 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p485 := by
    rcases h2710 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p486 := by
    rcases h2715 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p487 := by
    rcases h2720 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p488 := by
    rcases h2725 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h2602 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21305 (p477 p480 p489 p490 p491 p493 : Prop)
    (h21300 : p493 ∨ p477 ∨ p480)
    (h21301 : p489 ∨ p477 ∨ p480)
    (h21302 : p490 ∨ p477 ∨ p480)
    (h21303 : p491 ∨ p477 ∨ p480)
    (h21304 : (¬ p491) ∨ (¬ p489) ∨ p480 ∨ (¬ p493) ∨ p477 ∨ (¬ p490)) : p477 ∨ p480 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p477) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p480) := fun hu => hn (Or.inr hu)
  have u2 : p493 := by
    rcases h21300 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p489 := by
    rcases h21301 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p490 := by
    rcases h21302 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p491 := by
    rcases h21303 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21304 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (u0 q4)
  · exact False.elim (q5 u4)

theorem step21306 (p45 p48 p51 p52 p53 p54 p55 p56 : Prop)
    (h233 : p51 ∨ p56)
    (h238 : p52 ∨ p56)
    (h243 : p53 ∨ p56)
    (h248 : p54 ∨ p56)
    (h253 : p55 ∨ p56)
    (h144 : p45 ∨ p48 ∨ (¬ p51) ∨ (¬ p52) ∨ (¬ p53) ∨ (¬ p54) ∨ (¬ p55)) : p56 ∨ p48 ∨ p45 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p56) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p48) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p45) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p51 := by
    rcases h233 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p52 := by
    rcases h238 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p53 := by
    rcases h243 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p54 := by
    rcases h248 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p55 := by
    rcases h253 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h144 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21307 (p45 p48 p51 p52 p53 p54 p55 p57 : Prop)
    (h234 : p51 ∨ p57)
    (h239 : p52 ∨ p57)
    (h244 : p53 ∨ p57)
    (h249 : p54 ∨ p57)
    (h254 : p55 ∨ p57)
    (h144 : p45 ∨ p48 ∨ (¬ p51) ∨ (¬ p52) ∨ (¬ p53) ∨ (¬ p54) ∨ (¬ p55)) : p57 ∨ p48 ∨ p45 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p57) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p48) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p45) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p51 := by
    rcases h234 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p52 := by
    rcases h239 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p53 := by
    rcases h244 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p54 := by
    rcases h249 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p55 := by
    rcases h254 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h144 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21308 (p45 p48 p51 p52 p53 p54 p55 p58 : Prop)
    (h235 : p51 ∨ p58)
    (h240 : p52 ∨ p58)
    (h245 : p53 ∨ p58)
    (h250 : p54 ∨ p58)
    (h255 : p55 ∨ p58)
    (h144 : p45 ∨ p48 ∨ (¬ p51) ∨ (¬ p52) ∨ (¬ p53) ∨ (¬ p54) ∨ (¬ p55)) : p58 ∨ p48 ∨ p45 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p58) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p48) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p45) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p51 := by
    rcases h235 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p52 := by
    rcases h240 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p53 := by
    rcases h245 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p54 := by
    rcases h250 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p55 := by
    rcases h255 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h144 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21309 (p45 p48 p51 p52 p53 p54 p55 p59 : Prop)
    (h236 : p51 ∨ p59)
    (h241 : p52 ∨ p59)
    (h246 : p53 ∨ p59)
    (h251 : p54 ∨ p59)
    (h256 : p55 ∨ p59)
    (h144 : p45 ∨ p48 ∨ (¬ p51) ∨ (¬ p52) ∨ (¬ p53) ∨ (¬ p54) ∨ (¬ p55)) : p59 ∨ p48 ∨ p45 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p59) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p48) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p45) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p51 := by
    rcases h236 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p52 := by
    rcases h241 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p53 := by
    rcases h246 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p54 := by
    rcases h251 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p55 := by
    rcases h256 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h144 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21310 (p44 p45 p48 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 : Prop)
    (h21306 : p56 ∨ p48 ∨ p45)
    (h21307 : p57 ∨ p48 ∨ p45)
    (h21308 : p58 ∨ p48 ∨ p45)
    (h21309 : p59 ∨ p48 ∨ p45)
    (h164 : p44 ∨ p48 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60))
    (h237 : p51 ∨ p60)
    (h242 : p52 ∨ p60)
    (h247 : p53 ∨ p60)
    (h252 : p54 ∨ p60)
    (h257 : p55 ∨ p60)
    (h144 : p45 ∨ p48 ∨ (¬ p51) ∨ (¬ p52) ∨ (¬ p53) ∨ (¬ p54) ∨ (¬ p55)) : p48 ∨ p45 ∨ p44 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p48) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p45) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p44) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p56 := by
    rcases h21306 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p57 := by
    rcases h21307 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p58 := by
    rcases h21308 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p59 := by
    rcases h21309 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p60) := by
    rcases h164 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p51 := by
    rcases h237 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p52 := by
    rcases h242 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p53 := by
    rcases h247 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p54 := by
    rcases h252 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u12 : p55 := by
    rcases h257 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h144 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u12)

theorem step21311 (p15 p64 p73 p74 p75 p76 p77 p82 : Prop)
    (h373 : p73 ∨ p82)
    (h378 : p74 ∨ p82)
    (h383 : p75 ∨ p82)
    (h388 : p76 ∨ p82)
    (h393 : p77 ∨ p82)
    (h271 : p15 ∨ p64 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77)) : p82 ∨ p64 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p82) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p64) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p73 := by
    rcases h373 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p74 := by
    rcases h378 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p75 := by
    rcases h383 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p76 := by
    rcases h388 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p77 := by
    rcases h393 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h271 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21312 (p15 p64 p73 p74 p75 p76 p77 p78 : Prop)
    (h369 : p73 ∨ p78)
    (h374 : p74 ∨ p78)
    (h379 : p75 ∨ p78)
    (h384 : p76 ∨ p78)
    (h389 : p77 ∨ p78)
    (h271 : p15 ∨ p64 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77)) : p78 ∨ p64 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p78) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p64) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h271 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21313 (p15 p64 p73 p74 p75 p76 p77 p79 : Prop)
    (h370 : p73 ∨ p79)
    (h375 : p74 ∨ p79)
    (h380 : p75 ∨ p79)
    (h385 : p76 ∨ p79)
    (h390 : p77 ∨ p79)
    (h271 : p15 ∨ p64 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77)) : p79 ∨ p64 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p79) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p64) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p73 := by
    rcases h370 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p74 := by
    rcases h375 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p75 := by
    rcases h380 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p76 := by
    rcases h385 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p77 := by
    rcases h390 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h271 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21314 (p15 p64 p73 p74 p75 p76 p77 p80 : Prop)
    (h371 : p73 ∨ p80)
    (h376 : p74 ∨ p80)
    (h381 : p75 ∨ p80)
    (h386 : p76 ∨ p80)
    (h391 : p77 ∨ p80)
    (h271 : p15 ∨ p64 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77)) : p80 ∨ p64 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p80) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p64) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p73 := by
    rcases h371 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p74 := by
    rcases h376 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p75 := by
    rcases h381 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p76 := by
    rcases h386 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p77 := by
    rcases h391 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h271 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21315 (p15 p64 p73 p74 p75 p76 p77 p78 p79 p80 p81 p82 : Prop)
    (h296 : p15 ∨ p64 ∨ (¬ p78) ∨ (¬ p79) ∨ (¬ p80) ∨ (¬ p81) ∨ (¬ p82))
    (h372 : p73 ∨ p81)
    (h377 : p74 ∨ p81)
    (h382 : p75 ∨ p81)
    (h387 : p76 ∨ p81)
    (h392 : p77 ∨ p81)
    (h271 : p15 ∨ p64 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77)) : (¬ p80) ∨ p64 ∨ p15 ∨ (¬ p82) ∨ (¬ p79) ∨ (¬ p78) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p80 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p64) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p82 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p79 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p78 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p81) := by
    rcases h296 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u0)
    · exact q5
    · exact False.elim (q6 u3)
  have u7 : p73 := by
    rcases h372 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p74 := by
    rcases h377 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p75 := by
    rcases h382 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p76 := by
    rcases h387 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p77 := by
    rcases h392 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h271 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21316 (p15 p64 p78 p79 p80 p82 : Prop)
    (h21311 : p82 ∨ p64 ∨ p15)
    (h21312 : p78 ∨ p64 ∨ p15)
    (h21313 : p79 ∨ p64 ∨ p15)
    (h21314 : p80 ∨ p64 ∨ p15)
    (h21315 : (¬ p80) ∨ p64 ∨ p15 ∨ (¬ p82) ∨ (¬ p79) ∨ (¬ p78)) : p64 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p64) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr hu)
  have u2 : p82 := by
    rcases h21311 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p78 := by
    rcases h21312 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p79 := by
    rcases h21313 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p80 := by
    rcases h21314 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21315 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step21317 (p44 p48 p51 p52 p53 p54 p55 p60 : Prop)
    (h237 : p51 ∨ p60)
    (h242 : p52 ∨ p60)
    (h247 : p53 ∨ p60)
    (h252 : p54 ∨ p60)
    (h257 : p55 ∨ p60)
    (h139 : p44 ∨ p48 ∨ (¬ p51) ∨ (¬ p52) ∨ (¬ p53) ∨ (¬ p54) ∨ (¬ p55)) : p60 ∨ p48 ∨ p44 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p60) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p48) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p44) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p51 := by
    rcases h237 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p52 := by
    rcases h242 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p53 := by
    rcases h247 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p54 := by
    rcases h252 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p55 := by
    rcases h257 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h139 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21318 (p41 p44 p45 p48 p51 p56 p57 p58 p59 p60 : Prop)
    (h21317 : p60 ∨ p48 ∨ p44)
    (h21310 : p48 ∨ p45 ∨ p44)
    (h6739 : (¬ p41) ∨ (¬ p45))
    (h233 : p51 ∨ p56)
    (h234 : p51 ∨ p57)
    (h235 : p51 ∨ p58)
    (h236 : p51 ∨ p59)
    (h165 : p41 ∨ p44 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60)) : p51 ∨ p48 ∨ p44 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p51) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p48) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p44) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p60 := by
    rcases h21317 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p45 := by
    rcases h21310 with q0 | q1 | q2
    · exact False.elim (u1 q0)
    · exact q1
    · exact False.elim (u2 q2)
  have u5 : (¬ p41) := by
    rcases h6739 with q0 | q1
    · exact q0
    · exact False.elim (q1 u4)
  have u6 : p56 := by
    rcases h233 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p57 := by
    rcases h234 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u8 : p58 := by
    rcases h235 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u9 : p59 := by
    rcases h236 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h165 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u5 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u3)

theorem step21319 (p41 p44 p45 p48 p52 p56 p57 p58 p59 p60 : Prop)
    (h21317 : p60 ∨ p48 ∨ p44)
    (h21310 : p48 ∨ p45 ∨ p44)
    (h6739 : (¬ p41) ∨ (¬ p45))
    (h238 : p52 ∨ p56)
    (h239 : p52 ∨ p57)
    (h240 : p52 ∨ p58)
    (h241 : p52 ∨ p59)
    (h165 : p41 ∨ p44 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60)) : p52 ∨ p48 ∨ p44 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p52) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p48) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p44) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p60 := by
    rcases h21317 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p45 := by
    rcases h21310 with q0 | q1 | q2
    · exact False.elim (u1 q0)
    · exact q1
    · exact False.elim (u2 q2)
  have u5 : (¬ p41) := by
    rcases h6739 with q0 | q1
    · exact q0
    · exact False.elim (q1 u4)
  have u6 : p56 := by
    rcases h238 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p57 := by
    rcases h239 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u8 : p58 := by
    rcases h240 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u9 : p59 := by
    rcases h241 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h165 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u5 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u3)

theorem step21320 (p41 p44 p45 p48 p53 p56 p57 p58 p59 p60 : Prop)
    (h21317 : p60 ∨ p48 ∨ p44)
    (h21310 : p48 ∨ p45 ∨ p44)
    (h6739 : (¬ p41) ∨ (¬ p45))
    (h243 : p53 ∨ p56)
    (h244 : p53 ∨ p57)
    (h245 : p53 ∨ p58)
    (h246 : p53 ∨ p59)
    (h165 : p41 ∨ p44 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60)) : p53 ∨ p48 ∨ p44 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p53) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p48) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p44) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p60 := by
    rcases h21317 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p45 := by
    rcases h21310 with q0 | q1 | q2
    · exact False.elim (u1 q0)
    · exact q1
    · exact False.elim (u2 q2)
  have u5 : (¬ p41) := by
    rcases h6739 with q0 | q1
    · exact q0
    · exact False.elim (q1 u4)
  have u6 : p56 := by
    rcases h243 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p57 := by
    rcases h244 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u8 : p58 := by
    rcases h245 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u9 : p59 := by
    rcases h246 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h165 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u5 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u3)

theorem step21321 (p41 p44 p45 p48 p54 p56 p57 p58 p59 p60 : Prop)
    (h21317 : p60 ∨ p48 ∨ p44)
    (h21310 : p48 ∨ p45 ∨ p44)
    (h6739 : (¬ p41) ∨ (¬ p45))
    (h248 : p54 ∨ p56)
    (h249 : p54 ∨ p57)
    (h250 : p54 ∨ p58)
    (h251 : p54 ∨ p59)
    (h165 : p41 ∨ p44 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60)) : p54 ∨ p48 ∨ p44 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p54) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p48) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p44) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p60 := by
    rcases h21317 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p45 := by
    rcases h21310 with q0 | q1 | q2
    · exact False.elim (u1 q0)
    · exact q1
    · exact False.elim (u2 q2)
  have u5 : (¬ p41) := by
    rcases h6739 with q0 | q1
    · exact q0
    · exact False.elim (q1 u4)
  have u6 : p56 := by
    rcases h248 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p57 := by
    rcases h249 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u8 : p58 := by
    rcases h250 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u9 : p59 := by
    rcases h251 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h165 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u5 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u3)

theorem step21322 (p41 p44 p45 p48 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 : Prop)
    (h21310 : p48 ∨ p45 ∨ p44)
    (h6739 : (¬ p41) ∨ (¬ p45))
    (h21317 : p60 ∨ p48 ∨ p44)
    (h21318 : p51 ∨ p48 ∨ p44)
    (h21319 : p52 ∨ p48 ∨ p44)
    (h21320 : p53 ∨ p48 ∨ p44)
    (h21321 : p54 ∨ p48 ∨ p44)
    (h139 : p44 ∨ p48 ∨ (¬ p51) ∨ (¬ p52) ∨ (¬ p53) ∨ (¬ p54) ∨ (¬ p55))
    (h253 : p55 ∨ p56)
    (h254 : p55 ∨ p57)
    (h255 : p55 ∨ p58)
    (h256 : p55 ∨ p59)
    (h165 : p41 ∨ p44 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60)) : p48 ∨ p44 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p48) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p44) := fun hu => hn (Or.inr hu)
  have u2 : p45 := by
    rcases h21310 with q0 | q1 | q2
    · exact False.elim (u0 q0)
    · exact q1
    · exact False.elim (u1 q2)
  have u3 : (¬ p41) := by
    rcases h6739 with q0 | q1
    · exact q0
    · exact False.elim (q1 u2)
  have u4 : p60 := by
    rcases h21317 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p51 := by
    rcases h21318 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p52 := by
    rcases h21319 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : p53 := by
    rcases h21320 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u8 : p54 := by
    rcases h21321 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u9 : (¬ p55) := by
    rcases h139 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u6)
    · exact False.elim (q4 u7)
    · exact False.elim (q5 u8)
    · exact q6
  have u10 : p56 := by
    rcases h253 with q0 | q1
    · exact False.elim (u9 q0)
    · exact q1
  have u11 : p57 := by
    rcases h254 with q0 | q1
    · exact False.elim (u9 q0)
    · exact q1
  have u12 : p58 := by
    rcases h255 with q0 | q1
    · exact False.elim (u9 q0)
    · exact q1
  have u13 : p59 := by
    rcases h256 with q0 | q1
    · exact False.elim (u9 q0)
    · exact q1
  rcases h165 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u12)
  · exact False.elim (q5 u13)
  · exact False.elim (q6 u4)

theorem step21323 (p1096 p1099 p1105 p1106 p1107 p1108 p1109 p1110 p1111 p1112 p1113 p1114 : Prop)
    (h6516 : p1096 ∨ p1099 ∨ (¬ p1110) ∨ (¬ p1111) ∨ (¬ p1112) ∨ (¬ p1113) ∨ (¬ p1114))
    (h6583 : p1105 ∨ p1114)
    (h6588 : p1106 ∨ p1114)
    (h6593 : p1107 ∨ p1114)
    (h6598 : p1108 ∨ p1114)
    (h6603 : p1109 ∨ p1114)
    (h6491 : p1096 ∨ p1099 ∨ (¬ p1105) ∨ (¬ p1106) ∨ (¬ p1107) ∨ (¬ p1108) ∨ (¬ p1109)) : p1099 ∨ (¬ p1110) ∨ p1096 ∨ (¬ p1111) ∨ (¬ p1112) ∨ (¬ p1113) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1099) := fun hu => hn (Or.inl hu)
  have u1 : p1110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1111 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1112 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1113 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1114) := by
    rcases h6516 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u3)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact q6
  have u7 : p1105 := by
    rcases h6583 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1106 := by
    rcases h6588 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1107 := by
    rcases h6593 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1108 := by
    rcases h6598 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1109 := by
    rcases h6603 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h6491 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21324 (p532 p1452 p1455 p1456 p1457 p1458 p1459 p1464 : Prop)
    (h8887 : p1455 ∨ p1464)
    (h8892 : p1456 ∨ p1464)
    (h8897 : p1457 ∨ p1464)
    (h8902 : p1458 ∨ p1464)
    (h8907 : p1459 ∨ p1464)
    (h8795 : p532 ∨ p1452 ∨ (¬ p1455) ∨ (¬ p1456) ∨ (¬ p1457) ∨ (¬ p1458) ∨ (¬ p1459)) : p1464 ∨ p1452 ∨ p532 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1464) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1452) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p532) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1455 := by
    rcases h8887 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1456 := by
    rcases h8892 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1457 := by
    rcases h8897 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1458 := by
    rcases h8902 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1459 := by
    rcases h8907 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8795 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21325 (p532 p1452 p1455 p1456 p1457 p1458 p1459 p1460 : Prop)
    (h8883 : p1455 ∨ p1460)
    (h8888 : p1456 ∨ p1460)
    (h8893 : p1457 ∨ p1460)
    (h8898 : p1458 ∨ p1460)
    (h8903 : p1459 ∨ p1460)
    (h8795 : p532 ∨ p1452 ∨ (¬ p1455) ∨ (¬ p1456) ∨ (¬ p1457) ∨ (¬ p1458) ∨ (¬ p1459)) : p1460 ∨ p1452 ∨ p532 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1460) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1452) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p532) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1455 := by
    rcases h8883 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1456 := by
    rcases h8888 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1457 := by
    rcases h8893 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1458 := by
    rcases h8898 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1459 := by
    rcases h8903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8795 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21326 (p532 p1452 p1455 p1456 p1457 p1458 p1459 p1461 : Prop)
    (h8884 : p1455 ∨ p1461)
    (h8889 : p1456 ∨ p1461)
    (h8894 : p1457 ∨ p1461)
    (h8899 : p1458 ∨ p1461)
    (h8904 : p1459 ∨ p1461)
    (h8795 : p532 ∨ p1452 ∨ (¬ p1455) ∨ (¬ p1456) ∨ (¬ p1457) ∨ (¬ p1458) ∨ (¬ p1459)) : p1461 ∨ p1452 ∨ p532 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1461) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1452) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p532) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1455 := by
    rcases h8884 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1456 := by
    rcases h8889 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1457 := by
    rcases h8894 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1458 := by
    rcases h8899 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1459 := by
    rcases h8904 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8795 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21327 (p532 p1452 p1455 p1456 p1457 p1458 p1459 p1462 : Prop)
    (h8885 : p1455 ∨ p1462)
    (h8890 : p1456 ∨ p1462)
    (h8895 : p1457 ∨ p1462)
    (h8900 : p1458 ∨ p1462)
    (h8905 : p1459 ∨ p1462)
    (h8795 : p532 ∨ p1452 ∨ (¬ p1455) ∨ (¬ p1456) ∨ (¬ p1457) ∨ (¬ p1458) ∨ (¬ p1459)) : p1462 ∨ p1452 ∨ p532 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1462) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1452) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p532) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1455 := by
    rcases h8885 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1456 := by
    rcases h8890 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1457 := by
    rcases h8895 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1458 := by
    rcases h8900 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1459 := by
    rcases h8905 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8795 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21328 (p532 p1452 p1455 p1456 p1457 p1458 p1459 p1460 p1461 p1462 p1463 p1464 : Prop)
    (h8820 : p532 ∨ p1452 ∨ (¬ p1460) ∨ (¬ p1461) ∨ (¬ p1462) ∨ (¬ p1463) ∨ (¬ p1464))
    (h8886 : p1455 ∨ p1463)
    (h8891 : p1456 ∨ p1463)
    (h8896 : p1457 ∨ p1463)
    (h8901 : p1458 ∨ p1463)
    (h8906 : p1459 ∨ p1463)
    (h8795 : p532 ∨ p1452 ∨ (¬ p1455) ∨ (¬ p1456) ∨ (¬ p1457) ∨ (¬ p1458) ∨ (¬ p1459)) : (¬ p1462) ∨ (¬ p1464) ∨ p532 ∨ p1452 ∨ (¬ p1460) ∨ (¬ p1461) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1462 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1464 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p532) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1452) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1460 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1461 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1463) := by
    rcases h8820 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u0)
    · exact q5
    · exact False.elim (q6 u1)
  have u7 : p1455 := by
    rcases h8886 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1456 := by
    rcases h8891 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1457 := by
    rcases h8896 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1458 := by
    rcases h8901 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1459 := by
    rcases h8906 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h8795 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21329 (p532 p1452 p1460 p1461 p1462 p1464 : Prop)
    (h21324 : p1464 ∨ p1452 ∨ p532)
    (h21325 : p1460 ∨ p1452 ∨ p532)
    (h21326 : p1461 ∨ p1452 ∨ p532)
    (h21327 : p1462 ∨ p1452 ∨ p532)
    (h21328 : (¬ p1462) ∨ (¬ p1464) ∨ p532 ∨ p1452 ∨ (¬ p1460) ∨ (¬ p1461)) : p1452 ∨ p532 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1452) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p532) := fun hu => hn (Or.inr hu)
  have u2 : p1464 := by
    rcases h21324 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1460 := by
    rcases h21325 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1461 := by
    rcases h21326 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1462 := by
    rcases h21327 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21328 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step21330 (p574 p581 p584 p589 p590 p591 p592 p593 : Prop)
    (h3338 : p584 ∨ p589)
    (h3339 : p584 ∨ p590)
    (h3340 : p584 ∨ p591)
    (h3341 : p584 ∨ p592)
    (h3342 : p584 ∨ p593)
    (h3270 : p574 ∨ p581 ∨ (¬ p589) ∨ (¬ p590) ∨ (¬ p591) ∨ (¬ p592) ∨ (¬ p593)) : p584 ∨ p581 ∨ p574 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p584) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p581) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p574) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p589 := by
    rcases h3338 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p590 := by
    rcases h3339 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p591 := by
    rcases h3340 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p592 := by
    rcases h3341 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p593 := by
    rcases h3342 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3270 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21331 (p574 p581 p585 p589 p590 p591 p592 p593 : Prop)
    (h3343 : p585 ∨ p589)
    (h3344 : p585 ∨ p590)
    (h3345 : p585 ∨ p591)
    (h3346 : p585 ∨ p592)
    (h3347 : p585 ∨ p593)
    (h3270 : p574 ∨ p581 ∨ (¬ p589) ∨ (¬ p590) ∨ (¬ p591) ∨ (¬ p592) ∨ (¬ p593)) : p585 ∨ p581 ∨ p574 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p585) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p581) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p574) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p589 := by
    rcases h3343 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p590 := by
    rcases h3344 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p591 := by
    rcases h3345 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p592 := by
    rcases h3346 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p593 := by
    rcases h3347 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3270 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21332 (p574 p581 p586 p589 p590 p591 p592 p593 : Prop)
    (h3348 : p586 ∨ p589)
    (h3349 : p586 ∨ p590)
    (h3350 : p586 ∨ p591)
    (h3351 : p586 ∨ p592)
    (h3352 : p586 ∨ p593)
    (h3270 : p574 ∨ p581 ∨ (¬ p589) ∨ (¬ p590) ∨ (¬ p591) ∨ (¬ p592) ∨ (¬ p593)) : p586 ∨ p581 ∨ p574 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p586) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p581) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p574) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h3270 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21333 (p574 p581 p587 p589 p590 p591 p592 p593 : Prop)
    (h3353 : p587 ∨ p589)
    (h3354 : p587 ∨ p590)
    (h3355 : p587 ∨ p591)
    (h3356 : p587 ∨ p592)
    (h3357 : p587 ∨ p593)
    (h3270 : p574 ∨ p581 ∨ (¬ p589) ∨ (¬ p590) ∨ (¬ p591) ∨ (¬ p592) ∨ (¬ p593)) : p587 ∨ p581 ∨ p574 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p587) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p581) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p574) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p589 := by
    rcases h3353 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p590 := by
    rcases h3354 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p591 := by
    rcases h3355 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p592 := by
    rcases h3356 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p593 := by
    rcases h3357 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3270 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21335 (p860 p861 p865 p866 p867 p868 p869 p873 : Prop)
    (h5030 : p865 ∨ p873)
    (h5035 : p866 ∨ p873)
    (h5040 : p867 ∨ p873)
    (h5045 : p868 ∨ p873)
    (h5050 : p869 ∨ p873)
    (h4947 : p860 ∨ p861 ∨ (¬ p865) ∨ (¬ p866) ∨ (¬ p867) ∨ (¬ p868) ∨ (¬ p869)) : p873 ∨ p860 ∨ p861 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p873) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p860) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p861) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p865 := by
    rcases h5030 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p866 := by
    rcases h5035 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p867 := by
    rcases h5040 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p868 := by
    rcases h5045 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p869 := by
    rcases h5050 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4947 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21336 (p860 p861 p865 p866 p867 p868 p869 p874 : Prop)
    (h5031 : p865 ∨ p874)
    (h5036 : p866 ∨ p874)
    (h5041 : p867 ∨ p874)
    (h5046 : p868 ∨ p874)
    (h5051 : p869 ∨ p874)
    (h4947 : p860 ∨ p861 ∨ (¬ p865) ∨ (¬ p866) ∨ (¬ p867) ∨ (¬ p868) ∨ (¬ p869)) : p874 ∨ p860 ∨ p861 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p874) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p860) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p861) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p865 := by
    rcases h5031 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p866 := by
    rcases h5036 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p867 := by
    rcases h5041 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p868 := by
    rcases h5046 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p869 := by
    rcases h5051 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4947 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21337 (p860 p861 p865 p866 p867 p868 p869 p870 : Prop)
    (h5027 : p865 ∨ p870)
    (h5032 : p866 ∨ p870)
    (h5037 : p867 ∨ p870)
    (h5042 : p868 ∨ p870)
    (h5047 : p869 ∨ p870)
    (h4947 : p860 ∨ p861 ∨ (¬ p865) ∨ (¬ p866) ∨ (¬ p867) ∨ (¬ p868) ∨ (¬ p869)) : p870 ∨ p860 ∨ p861 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p870) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p860) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p861) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p865 := by
    rcases h5027 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p866 := by
    rcases h5032 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p867 := by
    rcases h5037 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p868 := by
    rcases h5042 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p869 := by
    rcases h5047 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4947 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21338 (p860 p861 p865 p866 p867 p868 p869 p871 : Prop)
    (h5028 : p865 ∨ p871)
    (h5033 : p866 ∨ p871)
    (h5038 : p867 ∨ p871)
    (h5043 : p868 ∨ p871)
    (h5048 : p869 ∨ p871)
    (h4947 : p860 ∨ p861 ∨ (¬ p865) ∨ (¬ p866) ∨ (¬ p867) ∨ (¬ p868) ∨ (¬ p869)) : p871 ∨ p860 ∨ p861 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p871) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p860) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p861) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p865 := by
    rcases h5028 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p866 := by
    rcases h5033 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p867 := by
    rcases h5038 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p868 := by
    rcases h5043 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p869 := by
    rcases h5048 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4947 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21339 (p860 p861 p865 p866 p867 p868 p869 p870 p871 p872 p873 p874 : Prop)
    (h4972 : p860 ∨ p861 ∨ (¬ p870) ∨ (¬ p871) ∨ (¬ p872) ∨ (¬ p873) ∨ (¬ p874))
    (h5029 : p865 ∨ p872)
    (h5034 : p866 ∨ p872)
    (h5039 : p867 ∨ p872)
    (h5044 : p868 ∨ p872)
    (h5049 : p869 ∨ p872)
    (h4947 : p860 ∨ p861 ∨ (¬ p865) ∨ (¬ p866) ∨ (¬ p867) ∨ (¬ p868) ∨ (¬ p869)) : (¬ p871) ∨ (¬ p874) ∨ p861 ∨ (¬ p870) ∨ (¬ p873) ∨ p860 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p871 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p874 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p861) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p870 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p873 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p860) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p872) := by
    rcases h4972 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u5 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u0)
    · exact q4
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u1)
  have u7 : p865 := by
    rcases h5029 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p866 := by
    rcases h5034 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p867 := by
    rcases h5039 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p868 := by
    rcases h5044 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p869 := by
    rcases h5049 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h4947 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u5 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21340 (p860 p861 p870 p871 p873 p874 : Prop)
    (h21335 : p873 ∨ p860 ∨ p861)
    (h21336 : p874 ∨ p860 ∨ p861)
    (h21337 : p870 ∨ p860 ∨ p861)
    (h21338 : p871 ∨ p860 ∨ p861)
    (h21339 : (¬ p871) ∨ (¬ p874) ∨ p861 ∨ (¬ p870) ∨ (¬ p873) ∨ p860) : p860 ∨ p861 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p860) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p861) := fun hu => hn (Or.inr hu)
  have u2 : p873 := by
    rcases h21335 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p874 := by
    rcases h21336 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p870 := by
    rcases h21337 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p871 := by
    rcases h21338 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21339 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u2)
  · exact False.elim (u0 q5)

theorem step21341 (p1229 p1233 p1239 p1240 p1241 p1242 p1243 p1247 : Prop)
    (h7431 : p1239 ∨ p1247)
    (h7436 : p1240 ∨ p1247)
    (h7441 : p1241 ∨ p1247)
    (h7446 : p1242 ∨ p1247)
    (h7451 : p1243 ∨ p1247)
    (h7345 : p1229 ∨ p1233 ∨ (¬ p1239) ∨ (¬ p1240) ∨ (¬ p1241) ∨ (¬ p1242) ∨ (¬ p1243)) : p1247 ∨ p1233 ∨ p1229 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1247) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1233) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h7345 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21342 (p1229 p1233 p1239 p1244 p1245 p1246 p1247 p1248 : Prop)
    (h21341 : p1247 ∨ p1233 ∨ p1229)
    (h7428 : p1239 ∨ p1244)
    (h7429 : p1239 ∨ p1245)
    (h7430 : p1239 ∨ p1246)
    (h7432 : p1239 ∨ p1248)
    (h7370 : p1229 ∨ p1233 ∨ (¬ p1244) ∨ (¬ p1245) ∨ (¬ p1246) ∨ (¬ p1247) ∨ (¬ p1248)) : p1239 ∨ p1233 ∨ p1229 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1239) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1233) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1247 := by
    rcases h21341 with q0 | q1 | q2
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
  rcases h7370 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step21343 (p1229 p1233 p1240 p1244 p1245 p1246 p1247 p1248 : Prop)
    (h21341 : p1247 ∨ p1233 ∨ p1229)
    (h7433 : p1240 ∨ p1244)
    (h7434 : p1240 ∨ p1245)
    (h7435 : p1240 ∨ p1246)
    (h7437 : p1240 ∨ p1248)
    (h7370 : p1229 ∨ p1233 ∨ (¬ p1244) ∨ (¬ p1245) ∨ (¬ p1246) ∨ (¬ p1247) ∨ (¬ p1248)) : p1240 ∨ p1233 ∨ p1229 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1240) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1233) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1247 := by
    rcases h21341 with q0 | q1 | q2
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
  rcases h7370 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step21344 (p1229 p1233 p1241 p1244 p1245 p1246 p1247 p1248 : Prop)
    (h21341 : p1247 ∨ p1233 ∨ p1229)
    (h7438 : p1241 ∨ p1244)
    (h7439 : p1241 ∨ p1245)
    (h7440 : p1241 ∨ p1246)
    (h7442 : p1241 ∨ p1248)
    (h7370 : p1229 ∨ p1233 ∨ (¬ p1244) ∨ (¬ p1245) ∨ (¬ p1246) ∨ (¬ p1247) ∨ (¬ p1248)) : p1241 ∨ p1233 ∨ p1229 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1241) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1233) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1247 := by
    rcases h21341 with q0 | q1 | q2
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
  rcases h7370 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step21345 (p1229 p1233 p1242 p1244 p1245 p1246 p1247 p1248 : Prop)
    (h21341 : p1247 ∨ p1233 ∨ p1229)
    (h7443 : p1242 ∨ p1244)
    (h7444 : p1242 ∨ p1245)
    (h7445 : p1242 ∨ p1246)
    (h7447 : p1242 ∨ p1248)
    (h7370 : p1229 ∨ p1233 ∨ (¬ p1244) ∨ (¬ p1245) ∨ (¬ p1246) ∨ (¬ p1247) ∨ (¬ p1248)) : p1242 ∨ p1233 ∨ p1229 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1242) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1233) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1247 := by
    rcases h21341 with q0 | q1 | q2
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
  rcases h7370 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step21346 (p1229 p1233 p1239 p1240 p1241 p1242 p1243 p1244 p1245 p1246 p1247 p1248 : Prop)
    (h21341 : p1247 ∨ p1233 ∨ p1229)
    (h21342 : p1239 ∨ p1233 ∨ p1229)
    (h21343 : p1240 ∨ p1233 ∨ p1229)
    (h21344 : p1241 ∨ p1233 ∨ p1229)
    (h21345 : p1242 ∨ p1233 ∨ p1229)
    (h7345 : p1229 ∨ p1233 ∨ (¬ p1239) ∨ (¬ p1240) ∨ (¬ p1241) ∨ (¬ p1242) ∨ (¬ p1243))
    (h7448 : p1243 ∨ p1244)
    (h7449 : p1243 ∨ p1245)
    (h7450 : p1243 ∨ p1246)
    (h7452 : p1243 ∨ p1248)
    (h7370 : p1229 ∨ p1233 ∨ (¬ p1244) ∨ (¬ p1245) ∨ (¬ p1246) ∨ (¬ p1247) ∨ (¬ p1248)) : p1233 ∨ p1229 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1233) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1229) := fun hu => hn (Or.inr hu)
  have u2 : p1247 := by
    rcases h21341 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1239 := by
    rcases h21342 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1240 := by
    rcases h21343 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1241 := by
    rcases h21344 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p1242 := by
    rcases h21345 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p1243) := by
    rcases h7345 with q0 | q1 | q2 | q3 | q4 | q5 | q6
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
  rcases h7370 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u11)

theorem step21347 (p364 p368 p371 p372 p373 p374 p375 p380 : Prop)
    (h2058 : p371 ∨ p380)
    (h2063 : p372 ∨ p380)
    (h2068 : p373 ∨ p380)
    (h2073 : p374 ∨ p380)
    (h2078 : p375 ∨ p380)
    (h1960 : p364 ∨ p368 ∨ (¬ p371) ∨ (¬ p372) ∨ (¬ p373) ∨ (¬ p374) ∨ (¬ p375)) : p380 ∨ p368 ∨ p364 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p380) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p368) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p364) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h1960 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21348 (p364 p368 p371 p376 p377 p378 p379 p380 : Prop)
    (h21347 : p380 ∨ p368 ∨ p364)
    (h2054 : p371 ∨ p376)
    (h2055 : p371 ∨ p377)
    (h2056 : p371 ∨ p378)
    (h2057 : p371 ∨ p379)
    (h1985 : p364 ∨ p368 ∨ (¬ p376) ∨ (¬ p377) ∨ (¬ p378) ∨ (¬ p379) ∨ (¬ p380)) : p371 ∨ p368 ∨ p364 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p371) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p368) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p364) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p380 := by
    rcases h21347 with q0 | q1 | q2
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
  rcases h1985 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step21349 (p364 p368 p372 p376 p377 p378 p379 p380 : Prop)
    (h21347 : p380 ∨ p368 ∨ p364)
    (h2059 : p372 ∨ p376)
    (h2060 : p372 ∨ p377)
    (h2061 : p372 ∨ p378)
    (h2062 : p372 ∨ p379)
    (h1985 : p364 ∨ p368 ∨ (¬ p376) ∨ (¬ p377) ∨ (¬ p378) ∨ (¬ p379) ∨ (¬ p380)) : p372 ∨ p368 ∨ p364 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p372) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p368) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p364) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p380 := by
    rcases h21347 with q0 | q1 | q2
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
  rcases h1985 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step21350 (p364 p368 p373 p376 p377 p378 p379 p380 : Prop)
    (h21347 : p380 ∨ p368 ∨ p364)
    (h2064 : p373 ∨ p376)
    (h2065 : p373 ∨ p377)
    (h2066 : p373 ∨ p378)
    (h2067 : p373 ∨ p379)
    (h1985 : p364 ∨ p368 ∨ (¬ p376) ∨ (¬ p377) ∨ (¬ p378) ∨ (¬ p379) ∨ (¬ p380)) : p373 ∨ p368 ∨ p364 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p373) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p368) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p364) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p380 := by
    rcases h21347 with q0 | q1 | q2
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
  rcases h1985 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step21351 (p364 p368 p374 p376 p377 p378 p379 p380 : Prop)
    (h21347 : p380 ∨ p368 ∨ p364)
    (h2069 : p374 ∨ p376)
    (h2070 : p374 ∨ p377)
    (h2071 : p374 ∨ p378)
    (h2072 : p374 ∨ p379)
    (h1985 : p364 ∨ p368 ∨ (¬ p376) ∨ (¬ p377) ∨ (¬ p378) ∨ (¬ p379) ∨ (¬ p380)) : p374 ∨ p368 ∨ p364 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p374) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p368) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p364) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p380 := by
    rcases h21347 with q0 | q1 | q2
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
  rcases h1985 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step21352 (p364 p368 p371 p372 p373 p374 p375 p376 p377 p378 p379 p380 : Prop)
    (h21347 : p380 ∨ p368 ∨ p364)
    (h21348 : p371 ∨ p368 ∨ p364)
    (h21349 : p372 ∨ p368 ∨ p364)
    (h21350 : p373 ∨ p368 ∨ p364)
    (h21351 : p374 ∨ p368 ∨ p364)
    (h1960 : p364 ∨ p368 ∨ (¬ p371) ∨ (¬ p372) ∨ (¬ p373) ∨ (¬ p374) ∨ (¬ p375))
    (h2074 : p375 ∨ p376)
    (h2075 : p375 ∨ p377)
    (h2076 : p375 ∨ p378)
    (h2077 : p375 ∨ p379)
    (h1985 : p364 ∨ p368 ∨ (¬ p376) ∨ (¬ p377) ∨ (¬ p378) ∨ (¬ p379) ∨ (¬ p380)) : p368 ∨ p364 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p368) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p364) := fun hu => hn (Or.inr hu)
  have u2 : p380 := by
    rcases h21347 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p371 := by
    rcases h21348 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p372 := by
    rcases h21349 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p373 := by
    rcases h21350 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p374 := by
    rcases h21351 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p375) := by
    rcases h1960 with q0 | q1 | q2 | q3 | q4 | q5 | q6
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
  rcases h1985 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u2)

theorem step21353 (p344 p345 p356 p357 p358 p359 p360 p361 : Prop)
    (h1945 : p356 ∨ p357)
    (h1946 : p356 ∨ p358)
    (h1947 : p356 ∨ p359)
    (h1948 : p356 ∨ p360)
    (h1852 : p344 ∨ p345 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361)) : p356 ∨ (¬ p361) ∨ p345 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p356) := fun hu => hn (Or.inl hu)
  have u1 : p361 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p345) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h1852 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21354 (p344 p345 p352 p353 p354 p355 p356 p357 : Prop)
    (h1925 : p352 ∨ p357)
    (h1930 : p353 ∨ p357)
    (h1935 : p354 ∨ p357)
    (h1940 : p355 ∨ p357)
    (h1827 : p344 ∨ p345 ∨ (¬ p352) ∨ (¬ p353) ∨ (¬ p354) ∨ (¬ p355) ∨ (¬ p356)) : p357 ∨ (¬ p356) ∨ p345 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p357) := fun hu => hn (Or.inl hu)
  have u1 : p356 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p345) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h1827 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21355 (p344 p345 p352 p353 p354 p355 p356 p358 : Prop)
    (h1926 : p352 ∨ p358)
    (h1931 : p353 ∨ p358)
    (h1936 : p354 ∨ p358)
    (h1941 : p355 ∨ p358)
    (h1827 : p344 ∨ p345 ∨ (¬ p352) ∨ (¬ p353) ∨ (¬ p354) ∨ (¬ p355) ∨ (¬ p356)) : p358 ∨ (¬ p356) ∨ p345 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p358) := fun hu => hn (Or.inl hu)
  have u1 : p356 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p345) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h1827 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21356 (p344 p345 p352 p353 p354 p355 p356 p359 : Prop)
    (h1927 : p352 ∨ p359)
    (h1932 : p353 ∨ p359)
    (h1937 : p354 ∨ p359)
    (h1942 : p355 ∨ p359)
    (h1827 : p344 ∨ p345 ∨ (¬ p352) ∨ (¬ p353) ∨ (¬ p354) ∨ (¬ p355) ∨ (¬ p356)) : p359 ∨ (¬ p356) ∨ p345 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p359) := fun hu => hn (Or.inl hu)
  have u1 : p356 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p345) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h1827 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21357 (p344 p345 p352 p353 p354 p355 p356 p357 p358 p359 p360 p361 : Prop)
    (h21353 : p356 ∨ (¬ p361) ∨ p345 ∨ p344)
    (h21354 : p357 ∨ (¬ p356) ∨ p345 ∨ p344)
    (h21355 : p358 ∨ (¬ p356) ∨ p345 ∨ p344)
    (h21356 : p359 ∨ (¬ p356) ∨ p345 ∨ p344)
    (h1852 : p344 ∨ p345 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361))
    (h1928 : p352 ∨ p360)
    (h1933 : p353 ∨ p360)
    (h1938 : p354 ∨ p360)
    (h1943 : p355 ∨ p360)
    (h1827 : p344 ∨ p345 ∨ (¬ p352) ∨ (¬ p353) ∨ (¬ p354) ∨ (¬ p355) ∨ (¬ p356)) : (¬ p361) ∨ p345 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p361 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p345) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p356 := by
    rcases h21353 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u4 : p357 := by
    rcases h21354 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u5 : p358 := by
    rcases h21355 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u6 : p359 := by
    rcases h21356 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u7 : (¬ p360) := by
    rcases h1852 with q0 | q1 | q2 | q3 | q4 | q5 | q6
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
  rcases h1827 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u3)

theorem step21358 (p344 p345 p352 p353 p354 p355 p356 p361 : Prop)
    (h21357 : (¬ p361) ∨ p345 ∨ p344)
    (h1929 : p352 ∨ p361)
    (h1934 : p353 ∨ p361)
    (h1939 : p354 ∨ p361)
    (h1944 : p355 ∨ p361)
    (h1949 : p356 ∨ p361)
    (h1827 : p344 ∨ p345 ∨ (¬ p352) ∨ (¬ p353) ∨ (¬ p354) ∨ (¬ p355) ∨ (¬ p356)) : p345 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p345) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p361) := by
    rcases h21357 with q0 | q1 | q2
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
  rcases h1827 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21359 (p345 p364 p368 p438 p687 p961 p1080 : Prop)
    (h12391 : (¬ p364) ∨ (¬ p438) ∨ (¬ p687))
    (h18246 : (¬ p345) ∨ (¬ p368) ∨ (¬ p438) ∨ (¬ p687) ∨ (¬ p961) ∨ (¬ p1080))
    (h21352 : p368 ∨ p364) : (¬ p438) ∨ (¬ p345) ∨ (¬ p961) ∨ (¬ p1080) ∨ (¬ p687) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p345 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1080 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p364) := by
    rcases h12391 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u4)
  have u6 : (¬ p368) := by
    rcases h18246 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u1)
    · exact q1
    · exact False.elim (q2 u0)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u2)
    · exact False.elim (q5 u3)
  rcases h21352 with q0 | q1
  · exact False.elim (u6 q0)
  · exact False.elim (u5 q1)

theorem step21360 (p1328 p1334 p1336 p1337 p1338 p1339 p1340 p1345 : Prop)
    (h8076 : p1336 ∨ p1345)
    (h8081 : p1337 ∨ p1345)
    (h8086 : p1338 ∨ p1345)
    (h8091 : p1339 ∨ p1345)
    (h8096 : p1340 ∨ p1345)
    (h7975 : p1328 ∨ p1334 ∨ (¬ p1336) ∨ (¬ p1337) ∨ (¬ p1338) ∨ (¬ p1339) ∨ (¬ p1340)) : p1345 ∨ p1334 ∨ p1328 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1345) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1334) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1328) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1336 := by
    rcases h8076 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1337 := by
    rcases h8081 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1338 := by
    rcases h8086 with q0 | q1
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
  rcases h7975 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21361 (p1328 p1334 p1336 p1337 p1338 p1339 p1340 p1341 : Prop)
    (h8072 : p1336 ∨ p1341)
    (h8077 : p1337 ∨ p1341)
    (h8082 : p1338 ∨ p1341)
    (h8087 : p1339 ∨ p1341)
    (h8092 : p1340 ∨ p1341)
    (h7975 : p1328 ∨ p1334 ∨ (¬ p1336) ∨ (¬ p1337) ∨ (¬ p1338) ∨ (¬ p1339) ∨ (¬ p1340)) : p1341 ∨ p1334 ∨ p1328 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1341) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1334) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1328) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1336 := by
    rcases h8072 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1337 := by
    rcases h8077 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1338 := by
    rcases h8082 with q0 | q1
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
  rcases h7975 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21362 (p1328 p1334 p1336 p1337 p1338 p1339 p1340 p1342 : Prop)
    (h8073 : p1336 ∨ p1342)
    (h8078 : p1337 ∨ p1342)
    (h8083 : p1338 ∨ p1342)
    (h8088 : p1339 ∨ p1342)
    (h8093 : p1340 ∨ p1342)
    (h7975 : p1328 ∨ p1334 ∨ (¬ p1336) ∨ (¬ p1337) ∨ (¬ p1338) ∨ (¬ p1339) ∨ (¬ p1340)) : p1342 ∨ p1334 ∨ p1328 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1342) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1334) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1328) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1336 := by
    rcases h8073 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1337 := by
    rcases h8078 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1338 := by
    rcases h8083 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1339 := by
    rcases h8088 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1340 := by
    rcases h8093 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7975 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21363 (p1328 p1334 p1336 p1337 p1338 p1339 p1340 p1343 : Prop)
    (h8074 : p1336 ∨ p1343)
    (h8079 : p1337 ∨ p1343)
    (h8084 : p1338 ∨ p1343)
    (h8089 : p1339 ∨ p1343)
    (h8094 : p1340 ∨ p1343)
    (h7975 : p1328 ∨ p1334 ∨ (¬ p1336) ∨ (¬ p1337) ∨ (¬ p1338) ∨ (¬ p1339) ∨ (¬ p1340)) : p1343 ∨ p1334 ∨ p1328 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1343) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1334) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1328) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1336 := by
    rcases h8074 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1337 := by
    rcases h8079 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1338 := by
    rcases h8084 with q0 | q1
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
  rcases h7975 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21364 (p1328 p1334 p1336 p1337 p1338 p1339 p1340 p1341 p1342 p1343 p1344 p1345 : Prop)
    (h8000 : p1328 ∨ p1334 ∨ (¬ p1341) ∨ (¬ p1342) ∨ (¬ p1343) ∨ (¬ p1344) ∨ (¬ p1345))
    (h8075 : p1336 ∨ p1344)
    (h8080 : p1337 ∨ p1344)
    (h8085 : p1338 ∨ p1344)
    (h8090 : p1339 ∨ p1344)
    (h8095 : p1340 ∨ p1344)
    (h7975 : p1328 ∨ p1334 ∨ (¬ p1336) ∨ (¬ p1337) ∨ (¬ p1338) ∨ (¬ p1339) ∨ (¬ p1340)) : (¬ p1343) ∨ (¬ p1341) ∨ p1328 ∨ (¬ p1345) ∨ p1334 ∨ (¬ p1342) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1343 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1341 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1328) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1345 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1334) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1342 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1344) := by
    rcases h8000 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u4 q1)
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u0)
    · exact q5
    · exact False.elim (q6 u3)
  have u7 : p1336 := by
    rcases h8075 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1337 := by
    rcases h8080 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1338 := by
    rcases h8085 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1339 := by
    rcases h8090 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1340 := by
    rcases h8095 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h7975 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21365 (p1328 p1334 p1341 p1342 p1343 p1345 : Prop)
    (h21360 : p1345 ∨ p1334 ∨ p1328)
    (h21361 : p1341 ∨ p1334 ∨ p1328)
    (h21362 : p1342 ∨ p1334 ∨ p1328)
    (h21363 : p1343 ∨ p1334 ∨ p1328)
    (h21364 : (¬ p1343) ∨ (¬ p1341) ∨ p1328 ∨ (¬ p1345) ∨ p1334 ∨ (¬ p1342)) : p1334 ∨ p1328 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1334) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1328) := fun hu => hn (Or.inr hu)
  have u2 : p1345 := by
    rcases h21360 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1341 := by
    rcases h21361 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1342 := by
    rcases h21362 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1343 := by
    rcases h21363 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21364 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (u0 q4)
  · exact False.elim (q5 u4)

theorem step21366 (p342 p344 p352 p353 p354 p355 p356 p361 : Prop)
    (h1929 : p352 ∨ p361)
    (h1934 : p353 ∨ p361)
    (h1939 : p354 ∨ p361)
    (h1944 : p355 ∨ p361)
    (h1949 : p356 ∨ p361)
    (h1842 : p342 ∨ p344 ∨ (¬ p352) ∨ (¬ p353) ∨ (¬ p354) ∨ (¬ p355) ∨ (¬ p356)) : p361 ∨ p342 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p361) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p342) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h1842 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21367 (p342 p344 p352 p353 p354 p355 p356 p357 p358 p359 p360 p361 : Prop)
    (h21114 : p352 ∨ (¬ p361) ∨ p342 ∨ p344)
    (h21115 : p353 ∨ (¬ p361) ∨ p342 ∨ p344)
    (h21116 : p354 ∨ (¬ p361) ∨ p342 ∨ p344)
    (h21117 : p355 ∨ (¬ p361) ∨ p342 ∨ p344)
    (h1842 : p342 ∨ p344 ∨ (¬ p352) ∨ (¬ p353) ∨ (¬ p354) ∨ (¬ p355) ∨ (¬ p356))
    (h1945 : p356 ∨ p357)
    (h1946 : p356 ∨ p358)
    (h1947 : p356 ∨ p359)
    (h1948 : p356 ∨ p360)
    (h1867 : p342 ∨ p344 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361)) : (¬ p361) ∨ p342 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p361 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p342) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p352 := by
    rcases h21114 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u4 : p353 := by
    rcases h21115 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u5 : p354 := by
    rcases h21116 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u6 : p355 := by
    rcases h21117 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u7 : (¬ p356) := by
    rcases h1842 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u2 q1)
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
  rcases h1867 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u0)

theorem step21368 (p342 p344 p361 : Prop)
    (h21366 : p361 ∨ p342 ∨ p344)
    (h21367 : (¬ p361) ∨ p342 ∨ p344) : p342 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p342) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr hu)
  have u2 : p361 := by
    rcases h21366 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21367 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)

theorem step21369 (p125 p368 p375 p376 p377 p378 p379 p380 : Prop)
    (h2074 : p375 ∨ p376)
    (h2075 : p375 ∨ p377)
    (h2076 : p375 ∨ p378)
    (h2077 : p375 ∨ p379)
    (h1990 : p125 ∨ p368 ∨ (¬ p376) ∨ (¬ p377) ∨ (¬ p378) ∨ (¬ p379) ∨ (¬ p380)) : p375 ∨ (¬ p380) ∨ p368 ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p375) := fun hu => hn (Or.inl hu)
  have u1 : p380 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p368) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p376 := by
    rcases h2074 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p377 := by
    rcases h2075 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p378 := by
    rcases h2076 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p379 := by
    rcases h2077 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1990 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21370 (p125 p368 p371 p372 p373 p374 p375 p376 : Prop)
    (h2054 : p371 ∨ p376)
    (h2059 : p372 ∨ p376)
    (h2064 : p373 ∨ p376)
    (h2069 : p374 ∨ p376)
    (h1965 : p125 ∨ p368 ∨ (¬ p371) ∨ (¬ p372) ∨ (¬ p373) ∨ (¬ p374) ∨ (¬ p375)) : p376 ∨ (¬ p375) ∨ p368 ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p376) := fun hu => hn (Or.inl hu)
  have u1 : p375 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p368) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p371 := by
    rcases h2054 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p372 := by
    rcases h2059 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p373 := by
    rcases h2064 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p374 := by
    rcases h2069 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1965 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21371 (p125 p368 p371 p372 p373 p374 p375 p377 : Prop)
    (h2055 : p371 ∨ p377)
    (h2060 : p372 ∨ p377)
    (h2065 : p373 ∨ p377)
    (h2070 : p374 ∨ p377)
    (h1965 : p125 ∨ p368 ∨ (¬ p371) ∨ (¬ p372) ∨ (¬ p373) ∨ (¬ p374) ∨ (¬ p375)) : p377 ∨ (¬ p375) ∨ p368 ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p377) := fun hu => hn (Or.inl hu)
  have u1 : p375 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p368) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p371 := by
    rcases h2055 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p372 := by
    rcases h2060 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p373 := by
    rcases h2065 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p374 := by
    rcases h2070 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1965 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21372 (p125 p368 p371 p372 p373 p374 p375 p378 : Prop)
    (h2056 : p371 ∨ p378)
    (h2061 : p372 ∨ p378)
    (h2066 : p373 ∨ p378)
    (h2071 : p374 ∨ p378)
    (h1965 : p125 ∨ p368 ∨ (¬ p371) ∨ (¬ p372) ∨ (¬ p373) ∨ (¬ p374) ∨ (¬ p375)) : p378 ∨ (¬ p375) ∨ p368 ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p378) := fun hu => hn (Or.inl hu)
  have u1 : p375 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p368) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p371 := by
    rcases h2056 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p372 := by
    rcases h2061 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p373 := by
    rcases h2066 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p374 := by
    rcases h2071 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1965 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21373 (p125 p368 p371 p372 p373 p374 p375 p376 p377 p378 p379 p380 : Prop)
    (h21369 : p375 ∨ (¬ p380) ∨ p368 ∨ p125)
    (h21370 : p376 ∨ (¬ p375) ∨ p368 ∨ p125)
    (h21371 : p377 ∨ (¬ p375) ∨ p368 ∨ p125)
    (h21372 : p378 ∨ (¬ p375) ∨ p368 ∨ p125)
    (h1990 : p125 ∨ p368 ∨ (¬ p376) ∨ (¬ p377) ∨ (¬ p378) ∨ (¬ p379) ∨ (¬ p380))
    (h2057 : p371 ∨ p379)
    (h2062 : p372 ∨ p379)
    (h2067 : p373 ∨ p379)
    (h2072 : p374 ∨ p379)
    (h1965 : p125 ∨ p368 ∨ (¬ p371) ∨ (¬ p372) ∨ (¬ p373) ∨ (¬ p374) ∨ (¬ p375)) : (¬ p380) ∨ p368 ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p380 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p368) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p375 := by
    rcases h21369 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u4 : p376 := by
    rcases h21370 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u5 : p377 := by
    rcases h21371 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u6 : p378 := by
    rcases h21372 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u7 : (¬ p379) := by
    rcases h1990 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u6)
    · exact q5
    · exact False.elim (q6 u0)
  have u8 : p371 := by
    rcases h2057 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p372 := by
    rcases h2062 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p373 := by
    rcases h2067 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p374 := by
    rcases h2072 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h1965 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u3)

theorem step21374 (p125 p368 p371 p372 p373 p374 p375 p380 : Prop)
    (h21373 : (¬ p380) ∨ p368 ∨ p125)
    (h2058 : p371 ∨ p380)
    (h2063 : p372 ∨ p380)
    (h2068 : p373 ∨ p380)
    (h2073 : p374 ∨ p380)
    (h2078 : p375 ∨ p380)
    (h1965 : p125 ∨ p368 ∨ (¬ p371) ∨ (¬ p372) ∨ (¬ p373) ∨ (¬ p374) ∨ (¬ p375)) : p368 ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p368) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p125) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p380) := by
    rcases h21373 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p371 := by
    rcases h2058 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : p372 := by
    rcases h2063 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p373 := by
    rcases h2068 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p374 := by
    rcases h2073 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p375 := by
    rcases h2078 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h1965 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21375 (p384 p387 p394 p395 p396 p397 p398 p399 : Prop)
    (h2201 : p394 ∨ p395)
    (h2202 : p394 ∨ p396)
    (h2203 : p394 ∨ p397)
    (h2205 : p394 ∨ p399)
    (h2113 : p384 ∨ p387 ∨ (¬ p395) ∨ (¬ p396) ∨ (¬ p397) ∨ (¬ p398) ∨ (¬ p399)) : p394 ∨ (¬ p398) ∨ p384 ∨ p387 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p394) := fun hu => hn (Or.inl hu)
  have u1 : p398 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p384) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p387) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p395 := by
    rcases h2201 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p396 := by
    rcases h2202 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p397 := by
    rcases h2203 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p399 := by
    rcases h2205 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2113 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step21376 (p384 p386 p390 p391 p392 p393 p394 p399 : Prop)
    (h2185 : p390 ∨ p399)
    (h2190 : p391 ∨ p399)
    (h2195 : p392 ∨ p399)
    (h2200 : p393 ∨ p399)
    (h2087 : p384 ∨ p386 ∨ (¬ p390) ∨ (¬ p391) ∨ (¬ p392) ∨ (¬ p393) ∨ (¬ p394)) : p399 ∨ (¬ p394) ∨ p384 ∨ p386 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p399) := fun hu => hn (Or.inl hu)
  have u1 : p394 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p384) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p386) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p390 := by
    rcases h2185 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p391 := by
    rcases h2190 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p392 := by
    rcases h2195 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p393 := by
    rcases h2200 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2087 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21377 (p384 p386 p390 p391 p392 p393 p394 p395 : Prop)
    (h2181 : p390 ∨ p395)
    (h2186 : p391 ∨ p395)
    (h2191 : p392 ∨ p395)
    (h2196 : p393 ∨ p395)
    (h2087 : p384 ∨ p386 ∨ (¬ p390) ∨ (¬ p391) ∨ (¬ p392) ∨ (¬ p393) ∨ (¬ p394)) : p395 ∨ (¬ p394) ∨ p384 ∨ p386 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p395) := fun hu => hn (Or.inl hu)
  have u1 : p394 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p384) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p386) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p390 := by
    rcases h2181 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p391 := by
    rcases h2186 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p392 := by
    rcases h2191 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p393 := by
    rcases h2196 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2087 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21378 (p384 p386 p390 p391 p392 p393 p394 p396 : Prop)
    (h2182 : p390 ∨ p396)
    (h2187 : p391 ∨ p396)
    (h2192 : p392 ∨ p396)
    (h2197 : p393 ∨ p396)
    (h2087 : p384 ∨ p386 ∨ (¬ p390) ∨ (¬ p391) ∨ (¬ p392) ∨ (¬ p393) ∨ (¬ p394)) : p396 ∨ (¬ p394) ∨ p384 ∨ p386 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p396) := fun hu => hn (Or.inl hu)
  have u1 : p394 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p384) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p386) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p390 := by
    rcases h2182 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p391 := by
    rcases h2187 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p392 := by
    rcases h2192 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p393 := by
    rcases h2197 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2087 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21379 (p384 p386 p387 p390 p391 p392 p393 p394 p395 p396 p397 p398 p399 : Prop)
    (h21375 : p394 ∨ (¬ p398) ∨ p384 ∨ p387)
    (h21376 : p399 ∨ (¬ p394) ∨ p384 ∨ p386)
    (h21377 : p395 ∨ (¬ p394) ∨ p384 ∨ p386)
    (h21378 : p396 ∨ (¬ p394) ∨ p384 ∨ p386)
    (h2112 : p384 ∨ p386 ∨ (¬ p395) ∨ (¬ p396) ∨ (¬ p397) ∨ (¬ p398) ∨ (¬ p399))
    (h2183 : p390 ∨ p397)
    (h2188 : p391 ∨ p397)
    (h2193 : p392 ∨ p397)
    (h2198 : p393 ∨ p397)
    (h2087 : p384 ∨ p386 ∨ (¬ p390) ∨ (¬ p391) ∨ (¬ p392) ∨ (¬ p393) ∨ (¬ p394)) : (¬ p398) ∨ p384 ∨ p386 ∨ p387 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p398 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p384) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p386) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p387) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p394 := by
    rcases h21375 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u3 q3)
  have u5 : p399 := by
    rcases h21376 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u4)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u6 : p395 := by
    rcases h21377 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u4)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u7 : p396 := by
    rcases h21378 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u4)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u8 : (¬ p397) := by
    rcases h2112 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u6)
    · exact False.elim (q3 u7)
    · exact q4
    · exact False.elim (q5 u0)
    · exact False.elim (q6 u5)
  have u9 : p390 := by
    rcases h2183 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u10 : p391 := by
    rcases h2188 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u11 : p392 := by
    rcases h2193 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u12 : p393 := by
    rcases h2198 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h2087 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u12)
  · exact False.elim (q6 u4)

theorem step21380 (p384 p386 p387 p390 p391 p392 p393 p394 p398 : Prop)
    (h21379 : (¬ p398) ∨ p384 ∨ p386 ∨ p387)
    (h2184 : p390 ∨ p398)
    (h2189 : p391 ∨ p398)
    (h2194 : p392 ∨ p398)
    (h2199 : p393 ∨ p398)
    (h2204 : p394 ∨ p398)
    (h2087 : p384 ∨ p386 ∨ (¬ p390) ∨ (¬ p391) ∨ (¬ p392) ∨ (¬ p393) ∨ (¬ p394)) : p384 ∨ p387 ∨ p386 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p384) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p387) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p386) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : (¬ p398) := by
    rcases h21379 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
    · exact False.elim (u1 q3)
  have u4 : p390 := by
    rcases h2184 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u5 : p391 := by
    rcases h2189 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p392 := by
    rcases h2194 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p393 := by
    rcases h2199 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p394 := by
    rcases h2204 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h2087 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u8)

theorem step21382 (p188 p192 p200 p201 p202 p203 p204 p205 : Prop)
    (h1042 : p200 ∨ p201)
    (h1043 : p200 ∨ p202)
    (h1044 : p200 ∨ p203)
    (h1045 : p200 ∨ p204)
    (h947 : p188 ∨ p192 ∨ (¬ p201) ∨ (¬ p202) ∨ (¬ p203) ∨ (¬ p204) ∨ (¬ p205)) : p200 ∨ (¬ p205) ∨ p188 ∨ p192 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p200) := fun hu => hn (Or.inl hu)
  have u1 : p205 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p188) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p192) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p201 := by
    rcases h1042 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p202 := by
    rcases h1043 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p203 := by
    rcases h1044 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p204 := by
    rcases h1045 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h947 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21383 (p188 p192 p196 p197 p198 p199 p200 p201 : Prop)
    (h1022 : p196 ∨ p201)
    (h1027 : p197 ∨ p201)
    (h1032 : p198 ∨ p201)
    (h1037 : p199 ∨ p201)
    (h922 : p188 ∨ p192 ∨ (¬ p196) ∨ (¬ p197) ∨ (¬ p198) ∨ (¬ p199) ∨ (¬ p200)) : p201 ∨ (¬ p200) ∨ p188 ∨ p192 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p201) := fun hu => hn (Or.inl hu)
  have u1 : p200 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p188) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p192) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p196 := by
    rcases h1022 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p197 := by
    rcases h1027 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p198 := by
    rcases h1032 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p199 := by
    rcases h1037 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h922 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21384 (p188 p192 p196 p197 p198 p199 p200 p202 : Prop)
    (h1023 : p196 ∨ p202)
    (h1028 : p197 ∨ p202)
    (h1033 : p198 ∨ p202)
    (h1038 : p199 ∨ p202)
    (h922 : p188 ∨ p192 ∨ (¬ p196) ∨ (¬ p197) ∨ (¬ p198) ∨ (¬ p199) ∨ (¬ p200)) : p202 ∨ (¬ p200) ∨ p188 ∨ p192 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p202) := fun hu => hn (Or.inl hu)
  have u1 : p200 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p188) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p192) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p196 := by
    rcases h1023 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p197 := by
    rcases h1028 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p198 := by
    rcases h1033 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p199 := by
    rcases h1038 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h922 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21385 (p188 p192 p196 p197 p198 p199 p200 p203 : Prop)
    (h1024 : p196 ∨ p203)
    (h1029 : p197 ∨ p203)
    (h1034 : p198 ∨ p203)
    (h1039 : p199 ∨ p203)
    (h922 : p188 ∨ p192 ∨ (¬ p196) ∨ (¬ p197) ∨ (¬ p198) ∨ (¬ p199) ∨ (¬ p200)) : p203 ∨ (¬ p200) ∨ p188 ∨ p192 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p203) := fun hu => hn (Or.inl hu)
  have u1 : p200 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p188) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p192) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p196 := by
    rcases h1024 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p197 := by
    rcases h1029 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p198 := by
    rcases h1034 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p199 := by
    rcases h1039 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h922 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21386 (p188 p192 p196 p197 p198 p199 p200 p201 p202 p203 p204 p205 : Prop)
    (h21382 : p200 ∨ (¬ p205) ∨ p188 ∨ p192)
    (h21383 : p201 ∨ (¬ p200) ∨ p188 ∨ p192)
    (h21384 : p202 ∨ (¬ p200) ∨ p188 ∨ p192)
    (h21385 : p203 ∨ (¬ p200) ∨ p188 ∨ p192)
    (h947 : p188 ∨ p192 ∨ (¬ p201) ∨ (¬ p202) ∨ (¬ p203) ∨ (¬ p204) ∨ (¬ p205))
    (h1025 : p196 ∨ p204)
    (h1030 : p197 ∨ p204)
    (h1035 : p198 ∨ p204)
    (h1040 : p199 ∨ p204)
    (h922 : p188 ∨ p192 ∨ (¬ p196) ∨ (¬ p197) ∨ (¬ p198) ∨ (¬ p199) ∨ (¬ p200)) : (¬ p205) ∨ p188 ∨ p192 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p205 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p188) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p192) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p200 := by
    rcases h21382 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u4 : p201 := by
    rcases h21383 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u5 : p202 := by
    rcases h21384 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u6 : p203 := by
    rcases h21385 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u7 : (¬ p204) := by
    rcases h947 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u6)
    · exact q5
    · exact False.elim (q6 u0)
  have u8 : p196 := by
    rcases h1025 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p197 := by
    rcases h1030 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p198 := by
    rcases h1035 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p199 := by
    rcases h1040 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h922 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u3)

theorem step21387 (p188 p192 p196 p197 p198 p199 p200 p205 : Prop)
    (h21386 : (¬ p205) ∨ p188 ∨ p192)
    (h1026 : p196 ∨ p205)
    (h1031 : p197 ∨ p205)
    (h1036 : p198 ∨ p205)
    (h1041 : p199 ∨ p205)
    (h1046 : p200 ∨ p205)
    (h922 : p188 ∨ p192 ∨ (¬ p196) ∨ (¬ p197) ∨ (¬ p198) ∨ (¬ p199) ∨ (¬ p200)) : p188 ∨ p192 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p188) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p192) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p205) := by
    rcases h21386 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p196 := by
    rcases h1026 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : p197 := by
    rcases h1031 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p198 := by
    rcases h1036 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p199 := by
    rcases h1041 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p200 := by
    rcases h1046 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h922 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21388 (p2 p187 p188 p189 p192 p193 p790 p797 p801 p814 : Prop)
    (h20735 : p790 ∨ p814)
    (h13697 : p187 ∨ p192)
    (h21387 : p188 ∨ p192)
    (h13685 : (¬ p2) ∨ (¬ p188) ∨ (¬ p801) ∨ p814)
    (h13696 : (¬ p187) ∨ (¬ p188) ∨ (¬ p193))
    (h21268 : p797 ∨ p801)
    (h21262 : p189 ∨ p193)
    (h7045 : (¬ p189) ∨ (¬ p790) ∨ (¬ p797)) : p192 ∨ p814 ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p192) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p814) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p790 := by
    rcases h20735 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u4 : p187 := by
    rcases h13697 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p188 := by
    rcases h21387 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : (¬ p801) := by
    rcases h13685 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u2)
    · exact False.elim (q1 u5)
    · exact q2
    · exact False.elim (u1 q3)
  have u7 : (¬ p193) := by
    rcases h13696 with q0 | q1 | q2
    · exact False.elim (q0 u4)
    · exact False.elim (q1 u5)
    · exact q2
  have u8 : p797 := by
    rcases h21268 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p189 := by
    rcases h21262 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h7045 with q0 | q1 | q2
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u8)

theorem step21389 (p303 p387 p390 p391 p392 p393 p394 p398 : Prop)
    (h2184 : p390 ∨ p398)
    (h2189 : p391 ∨ p398)
    (h2194 : p392 ∨ p398)
    (h2199 : p393 ∨ p398)
    (h2204 : p394 ∨ p398)
    (h2093 : p303 ∨ p387 ∨ (¬ p390) ∨ (¬ p391) ∨ (¬ p392) ∨ (¬ p393) ∨ (¬ p394)) : p398 ∨ p387 ∨ p303 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p398) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p387) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p303) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h2093 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21390 (p303 p387 p390 p395 p396 p397 p398 p399 : Prop)
    (h21389 : p398 ∨ p387 ∨ p303)
    (h2181 : p390 ∨ p395)
    (h2182 : p390 ∨ p396)
    (h2183 : p390 ∨ p397)
    (h2185 : p390 ∨ p399)
    (h2118 : p303 ∨ p387 ∨ (¬ p395) ∨ (¬ p396) ∨ (¬ p397) ∨ (¬ p398) ∨ (¬ p399)) : p390 ∨ p387 ∨ p303 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p390) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p387) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p303) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p398 := by
    rcases h21389 with q0 | q1 | q2
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
  rcases h2118 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step21391 (p303 p387 p391 p395 p396 p397 p398 p399 : Prop)
    (h21389 : p398 ∨ p387 ∨ p303)
    (h2186 : p391 ∨ p395)
    (h2187 : p391 ∨ p396)
    (h2188 : p391 ∨ p397)
    (h2190 : p391 ∨ p399)
    (h2118 : p303 ∨ p387 ∨ (¬ p395) ∨ (¬ p396) ∨ (¬ p397) ∨ (¬ p398) ∨ (¬ p399)) : p391 ∨ p387 ∨ p303 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p391) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p387) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p303) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p398 := by
    rcases h21389 with q0 | q1 | q2
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
  rcases h2118 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step21392 (p303 p387 p392 p395 p396 p397 p398 p399 : Prop)
    (h21389 : p398 ∨ p387 ∨ p303)
    (h2191 : p392 ∨ p395)
    (h2192 : p392 ∨ p396)
    (h2193 : p392 ∨ p397)
    (h2195 : p392 ∨ p399)
    (h2118 : p303 ∨ p387 ∨ (¬ p395) ∨ (¬ p396) ∨ (¬ p397) ∨ (¬ p398) ∨ (¬ p399)) : p392 ∨ p387 ∨ p303 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p392) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p387) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p303) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p398 := by
    rcases h21389 with q0 | q1 | q2
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
  rcases h2118 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step21393 (p303 p387 p393 p395 p396 p397 p398 p399 : Prop)
    (h21389 : p398 ∨ p387 ∨ p303)
    (h2196 : p393 ∨ p395)
    (h2197 : p393 ∨ p396)
    (h2198 : p393 ∨ p397)
    (h2200 : p393 ∨ p399)
    (h2118 : p303 ∨ p387 ∨ (¬ p395) ∨ (¬ p396) ∨ (¬ p397) ∨ (¬ p398) ∨ (¬ p399)) : p393 ∨ p387 ∨ p303 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p393) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p387) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p303) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p398 := by
    rcases h21389 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p395 := by
    rcases h2196 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p396 := by
    rcases h2197 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p397 := by
    rcases h2198 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p399 := by
    rcases h2200 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2118 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step21394 (p303 p387 p390 p391 p392 p393 p394 p395 p396 p397 p398 p399 : Prop)
    (h21389 : p398 ∨ p387 ∨ p303)
    (h21390 : p390 ∨ p387 ∨ p303)
    (h21391 : p391 ∨ p387 ∨ p303)
    (h21392 : p392 ∨ p387 ∨ p303)
    (h21393 : p393 ∨ p387 ∨ p303)
    (h2093 : p303 ∨ p387 ∨ (¬ p390) ∨ (¬ p391) ∨ (¬ p392) ∨ (¬ p393) ∨ (¬ p394))
    (h2201 : p394 ∨ p395)
    (h2202 : p394 ∨ p396)
    (h2203 : p394 ∨ p397)
    (h2205 : p394 ∨ p399)
    (h2118 : p303 ∨ p387 ∨ (¬ p395) ∨ (¬ p396) ∨ (¬ p397) ∨ (¬ p398) ∨ (¬ p399)) : p387 ∨ p303 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p387) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr hu)
  have u2 : p398 := by
    rcases h21389 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p390 := by
    rcases h21390 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p391 := by
    rcases h21391 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p392 := by
    rcases h21392 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p393 := by
    rcases h21393 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p394) := by
    rcases h2093 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p395 := by
    rcases h2201 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p396 := by
    rcases h2202 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p397 := by
    rcases h2203 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p399 := by
    rcases h2205 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h2118 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u11)

theorem step21395 (p858 p861 p865 p866 p867 p868 p869 p872 : Prop)
    (h5029 : p865 ∨ p872)
    (h5034 : p866 ∨ p872)
    (h5039 : p867 ∨ p872)
    (h5044 : p868 ∨ p872)
    (h5049 : p869 ∨ p872)
    (h4937 : p858 ∨ p861 ∨ (¬ p865) ∨ (¬ p866) ∨ (¬ p867) ∨ (¬ p868) ∨ (¬ p869)) : p872 ∨ p861 ∨ p858 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p872) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p861) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p858) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p865 := by
    rcases h5029 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p866 := by
    rcases h5034 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p867 := by
    rcases h5039 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p868 := by
    rcases h5044 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p869 := by
    rcases h5049 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4937 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21396 (p858 p861 p865 p866 p867 p868 p869 p873 : Prop)
    (h5030 : p865 ∨ p873)
    (h5035 : p866 ∨ p873)
    (h5040 : p867 ∨ p873)
    (h5045 : p868 ∨ p873)
    (h5050 : p869 ∨ p873)
    (h4937 : p858 ∨ p861 ∨ (¬ p865) ∨ (¬ p866) ∨ (¬ p867) ∨ (¬ p868) ∨ (¬ p869)) : p873 ∨ p861 ∨ p858 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p873) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p861) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p858) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p865 := by
    rcases h5030 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p866 := by
    rcases h5035 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p867 := by
    rcases h5040 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p868 := by
    rcases h5045 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p869 := by
    rcases h5050 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4937 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21397 (p858 p861 p865 p866 p867 p868 p869 p874 : Prop)
    (h5031 : p865 ∨ p874)
    (h5036 : p866 ∨ p874)
    (h5041 : p867 ∨ p874)
    (h5046 : p868 ∨ p874)
    (h5051 : p869 ∨ p874)
    (h4937 : p858 ∨ p861 ∨ (¬ p865) ∨ (¬ p866) ∨ (¬ p867) ∨ (¬ p868) ∨ (¬ p869)) : p874 ∨ p861 ∨ p858 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p874) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p861) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p858) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p865 := by
    rcases h5031 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p866 := by
    rcases h5036 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p867 := by
    rcases h5041 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p868 := by
    rcases h5046 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p869 := by
    rcases h5051 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4937 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21398 (p858 p861 p865 p866 p867 p868 p869 p870 : Prop)
    (h5027 : p865 ∨ p870)
    (h5032 : p866 ∨ p870)
    (h5037 : p867 ∨ p870)
    (h5042 : p868 ∨ p870)
    (h5047 : p869 ∨ p870)
    (h4937 : p858 ∨ p861 ∨ (¬ p865) ∨ (¬ p866) ∨ (¬ p867) ∨ (¬ p868) ∨ (¬ p869)) : p870 ∨ p861 ∨ p858 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p870) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p861) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p858) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p865 := by
    rcases h5027 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p866 := by
    rcases h5032 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p867 := by
    rcases h5037 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p868 := by
    rcases h5042 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p869 := by
    rcases h5047 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4937 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21399 (p858 p861 p865 p866 p867 p868 p869 p870 p871 p872 p873 p874 : Prop)
    (h4962 : p858 ∨ p861 ∨ (¬ p870) ∨ (¬ p871) ∨ (¬ p872) ∨ (¬ p873) ∨ (¬ p874))
    (h5028 : p865 ∨ p871)
    (h5033 : p866 ∨ p871)
    (h5038 : p867 ∨ p871)
    (h5043 : p868 ∨ p871)
    (h5048 : p869 ∨ p871)
    (h4937 : p858 ∨ p861 ∨ (¬ p865) ∨ (¬ p866) ∨ (¬ p867) ∨ (¬ p868) ∨ (¬ p869)) : (¬ p870) ∨ (¬ p873) ∨ p861 ∨ (¬ p874) ∨ p858 ∨ (¬ p872) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p870 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p873 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p861) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p874 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p858) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p872 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p871) := by
    rcases h4962 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u4 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u0)
    · exact q3
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u1)
    · exact False.elim (q6 u3)
  have u7 : p865 := by
    rcases h5028 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p866 := by
    rcases h5033 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p867 := by
    rcases h5038 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p868 := by
    rcases h5043 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p869 := by
    rcases h5048 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h4937 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21400 (p858 p861 p870 p872 p873 p874 : Prop)
    (h21395 : p872 ∨ p861 ∨ p858)
    (h21396 : p873 ∨ p861 ∨ p858)
    (h21397 : p874 ∨ p861 ∨ p858)
    (h21398 : p870 ∨ p861 ∨ p858)
    (h21399 : (¬ p870) ∨ (¬ p873) ∨ p861 ∨ (¬ p874) ∨ p858 ∨ (¬ p872)) : p861 ∨ p858 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p861) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p858) := fun hu => hn (Or.inr hu)
  have u2 : p872 := by
    rcases h21395 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p873 := by
    rcases h21396 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p874 := by
    rcases h21397 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p870 := by
    rcases h21398 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21399 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (u1 q4)
  · exact False.elim (q5 u2)

theorem step21401 (p420 p601 p604 p609 p610 p611 p612 p613 : Prop)
    (h3465 : p604 ∨ p609)
    (h3466 : p604 ∨ p610)
    (h3467 : p604 ∨ p611)
    (h3468 : p604 ∨ p612)
    (h3469 : p604 ∨ p613)
    (h3402 : p420 ∨ p601 ∨ (¬ p609) ∨ (¬ p610) ∨ (¬ p611) ∨ (¬ p612) ∨ (¬ p613)) : p604 ∨ p420 ∨ p601 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p604) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p420) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p601) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p609 := by
    rcases h3465 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p610 := by
    rcases h3466 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p611 := by
    rcases h3467 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p612 := by
    rcases h3468 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p613 := by
    rcases h3469 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3402 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21402 (p420 p601 p605 p609 p610 p611 p612 p613 : Prop)
    (h3470 : p605 ∨ p609)
    (h3471 : p605 ∨ p610)
    (h3472 : p605 ∨ p611)
    (h3473 : p605 ∨ p612)
    (h3474 : p605 ∨ p613)
    (h3402 : p420 ∨ p601 ∨ (¬ p609) ∨ (¬ p610) ∨ (¬ p611) ∨ (¬ p612) ∨ (¬ p613)) : p605 ∨ p420 ∨ p601 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p605) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p420) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p601) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p609 := by
    rcases h3470 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p610 := by
    rcases h3471 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p611 := by
    rcases h3472 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p612 := by
    rcases h3473 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p613 := by
    rcases h3474 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3402 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21403 (p420 p601 p606 p609 p610 p611 p612 p613 : Prop)
    (h3475 : p606 ∨ p609)
    (h3476 : p606 ∨ p610)
    (h3477 : p606 ∨ p611)
    (h3478 : p606 ∨ p612)
    (h3479 : p606 ∨ p613)
    (h3402 : p420 ∨ p601 ∨ (¬ p609) ∨ (¬ p610) ∨ (¬ p611) ∨ (¬ p612) ∨ (¬ p613)) : p606 ∨ p420 ∨ p601 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p606) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p420) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p601) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p609 := by
    rcases h3475 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p610 := by
    rcases h3476 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p611 := by
    rcases h3477 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p612 := by
    rcases h3478 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p613 := by
    rcases h3479 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3402 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21404 (p420 p601 p607 p609 p610 p611 p612 p613 : Prop)
    (h3480 : p607 ∨ p609)
    (h3481 : p607 ∨ p610)
    (h3482 : p607 ∨ p611)
    (h3483 : p607 ∨ p612)
    (h3484 : p607 ∨ p613)
    (h3402 : p420 ∨ p601 ∨ (¬ p609) ∨ (¬ p610) ∨ (¬ p611) ∨ (¬ p612) ∨ (¬ p613)) : p607 ∨ p420 ∨ p601 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p607) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p420) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p601) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p609 := by
    rcases h3480 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p610 := by
    rcases h3481 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p611 := by
    rcases h3482 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p612 := by
    rcases h3483 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p613 := by
    rcases h3484 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3402 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21405 (p420 p601 p604 p605 p606 p607 p608 p609 p610 p611 p612 p613 : Prop)
    (h3377 : p420 ∨ p601 ∨ (¬ p604) ∨ (¬ p605) ∨ (¬ p606) ∨ (¬ p607) ∨ (¬ p608))
    (h3485 : p608 ∨ p609)
    (h3486 : p608 ∨ p610)
    (h3487 : p608 ∨ p611)
    (h3488 : p608 ∨ p612)
    (h3489 : p608 ∨ p613)
    (h3402 : p420 ∨ p601 ∨ (¬ p609) ∨ (¬ p610) ∨ (¬ p611) ∨ (¬ p612) ∨ (¬ p613)) : (¬ p607) ∨ (¬ p606) ∨ p601 ∨ p420 ∨ (¬ p604) ∨ (¬ p605) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p607 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p606 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p601) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p604 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p605 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p608) := by
    rcases h3377 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p609 := by
    rcases h3485 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p610 := by
    rcases h3486 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p611 := by
    rcases h3487 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p612 := by
    rcases h3488 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p613 := by
    rcases h3489 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h3402 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21406 (p420 p601 p604 p605 p606 p607 : Prop)
    (h21401 : p604 ∨ p420 ∨ p601)
    (h21402 : p605 ∨ p420 ∨ p601)
    (h21403 : p606 ∨ p420 ∨ p601)
    (h21404 : p607 ∨ p420 ∨ p601)
    (h21405 : (¬ p607) ∨ (¬ p606) ∨ p601 ∨ p420 ∨ (¬ p604) ∨ (¬ p605)) : p420 ∨ p601 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p420) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p601) := fun hu => hn (Or.inr hu)
  have u2 : p604 := by
    rcases h21401 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p605 := by
    rcases h21402 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p606 := by
    rcases h21403 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p607 := by
    rcases h21404 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21405 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21407 (p258 p287 p291 p292 p293 p294 p295 p299 : Prop)
    (h1549 : p291 ∨ p299)
    (h1554 : p292 ∨ p299)
    (h1559 : p293 ∨ p299)
    (h1564 : p294 ∨ p299)
    (h1569 : p295 ∨ p299)
    (h1457 : p258 ∨ p287 ∨ (¬ p291) ∨ (¬ p292) ∨ (¬ p293) ∨ (¬ p294) ∨ (¬ p295)) : p299 ∨ p258 ∨ p287 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p299) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p258) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p287) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p291 := by
    rcases h1549 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p292 := by
    rcases h1554 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p293 := by
    rcases h1559 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p294 := by
    rcases h1564 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p295 := by
    rcases h1569 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1457 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21408 (p258 p288 p291 p296 p297 p298 p299 p300 : Prop)
    (h1546 : p291 ∨ p296)
    (h1547 : p291 ∨ p297)
    (h1548 : p291 ∨ p298)
    (h1550 : p291 ∨ p300)
    (h1483 : p258 ∨ p288 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300)) : p291 ∨ (¬ p299) ∨ p258 ∨ p288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p291) := fun hu => hn (Or.inl hu)
  have u1 : p299 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p288) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p296 := by
    rcases h1546 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p297 := by
    rcases h1547 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p298 := by
    rcases h1548 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p300 := by
    rcases h1550 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1483 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step21409 (p258 p288 p292 p296 p297 p298 p299 p300 : Prop)
    (h1551 : p292 ∨ p296)
    (h1552 : p292 ∨ p297)
    (h1553 : p292 ∨ p298)
    (h1555 : p292 ∨ p300)
    (h1483 : p258 ∨ p288 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300)) : p292 ∨ (¬ p299) ∨ p258 ∨ p288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p292) := fun hu => hn (Or.inl hu)
  have u1 : p299 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p288) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p296 := by
    rcases h1551 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p297 := by
    rcases h1552 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p298 := by
    rcases h1553 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p300 := by
    rcases h1555 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1483 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step21410 (p258 p288 p293 p296 p297 p298 p299 p300 : Prop)
    (h1556 : p293 ∨ p296)
    (h1557 : p293 ∨ p297)
    (h1558 : p293 ∨ p298)
    (h1560 : p293 ∨ p300)
    (h1483 : p258 ∨ p288 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300)) : p293 ∨ (¬ p299) ∨ p258 ∨ p288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p293) := fun hu => hn (Or.inl hu)
  have u1 : p299 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p288) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p296 := by
    rcases h1556 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p297 := by
    rcases h1557 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p298 := by
    rcases h1558 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p300 := by
    rcases h1560 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1483 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step21411 (p258 p288 p294 p296 p297 p298 p299 p300 : Prop)
    (h1561 : p294 ∨ p296)
    (h1562 : p294 ∨ p297)
    (h1563 : p294 ∨ p298)
    (h1565 : p294 ∨ p300)
    (h1483 : p258 ∨ p288 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300)) : p294 ∨ (¬ p299) ∨ p258 ∨ p288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p294) := fun hu => hn (Or.inl hu)
  have u1 : p299 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p288) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p296 := by
    rcases h1561 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p297 := by
    rcases h1562 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p298 := by
    rcases h1563 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p300 := by
    rcases h1565 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1483 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step21412 (p258 p288 p291 p292 p293 p294 p295 p296 p297 p298 p299 p300 : Prop)
    (h21408 : p291 ∨ (¬ p299) ∨ p258 ∨ p288)
    (h21409 : p292 ∨ (¬ p299) ∨ p258 ∨ p288)
    (h21410 : p293 ∨ (¬ p299) ∨ p258 ∨ p288)
    (h21411 : p294 ∨ (¬ p299) ∨ p258 ∨ p288)
    (h1458 : p258 ∨ p288 ∨ (¬ p291) ∨ (¬ p292) ∨ (¬ p293) ∨ (¬ p294) ∨ (¬ p295))
    (h1566 : p295 ∨ p296)
    (h1567 : p295 ∨ p297)
    (h1568 : p295 ∨ p298)
    (h1570 : p295 ∨ p300)
    (h1483 : p258 ∨ p288 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300)) : (¬ p299) ∨ p258 ∨ p288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p299 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p258) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p288) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p291 := by
    rcases h21408 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u4 : p292 := by
    rcases h21409 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u5 : p293 := by
    rcases h21410 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u6 : p294 := by
    rcases h21411 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u7 : (¬ p295) := by
    rcases h1458 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p296 := by
    rcases h1566 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p297 := by
    rcases h1567 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p298 := by
    rcases h1568 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p300 := by
    rcases h1570 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h1483 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u11)

theorem step21414 (p255 p288 p295 p296 p297 p298 p299 p300 : Prop)
    (h1566 : p295 ∨ p296)
    (h1567 : p295 ∨ p297)
    (h1568 : p295 ∨ p298)
    (h1570 : p295 ∨ p300)
    (h1478 : p255 ∨ p288 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300)) : p295 ∨ (¬ p299) ∨ p255 ∨ p288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p295) := fun hu => hn (Or.inl hu)
  have u1 : p299 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p255) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p288) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p296 := by
    rcases h1566 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p297 := by
    rcases h1567 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p298 := by
    rcases h1568 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p300 := by
    rcases h1570 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1478 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step21415 (p255 p288 p291 p292 p293 p294 p295 p300 : Prop)
    (h1550 : p291 ∨ p300)
    (h1555 : p292 ∨ p300)
    (h1560 : p293 ∨ p300)
    (h1565 : p294 ∨ p300)
    (h1453 : p255 ∨ p288 ∨ (¬ p291) ∨ (¬ p292) ∨ (¬ p293) ∨ (¬ p294) ∨ (¬ p295)) : p300 ∨ (¬ p295) ∨ p255 ∨ p288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p300) := fun hu => hn (Or.inl hu)
  have u1 : p295 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p255) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p288) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p291 := by
    rcases h1550 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p292 := by
    rcases h1555 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p293 := by
    rcases h1560 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p294 := by
    rcases h1565 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1453 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21416 (p255 p288 p291 p292 p293 p294 p295 p296 : Prop)
    (h1546 : p291 ∨ p296)
    (h1551 : p292 ∨ p296)
    (h1556 : p293 ∨ p296)
    (h1561 : p294 ∨ p296)
    (h1453 : p255 ∨ p288 ∨ (¬ p291) ∨ (¬ p292) ∨ (¬ p293) ∨ (¬ p294) ∨ (¬ p295)) : p296 ∨ (¬ p295) ∨ p255 ∨ p288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p296) := fun hu => hn (Or.inl hu)
  have u1 : p295 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p255) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p288) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p291 := by
    rcases h1546 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p292 := by
    rcases h1551 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p293 := by
    rcases h1556 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p294 := by
    rcases h1561 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1453 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21417 (p255 p288 p291 p292 p293 p294 p295 p297 : Prop)
    (h1547 : p291 ∨ p297)
    (h1552 : p292 ∨ p297)
    (h1557 : p293 ∨ p297)
    (h1562 : p294 ∨ p297)
    (h1453 : p255 ∨ p288 ∨ (¬ p291) ∨ (¬ p292) ∨ (¬ p293) ∨ (¬ p294) ∨ (¬ p295)) : p297 ∨ (¬ p295) ∨ p255 ∨ p288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p297) := fun hu => hn (Or.inl hu)
  have u1 : p295 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p255) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p288) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p291 := by
    rcases h1547 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p292 := by
    rcases h1552 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p293 := by
    rcases h1557 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p294 := by
    rcases h1562 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1453 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21418 (p255 p287 p288 p291 p292 p293 p294 p295 p296 p297 p298 p299 p300 : Prop)
    (h21414 : p295 ∨ (¬ p299) ∨ p255 ∨ p288)
    (h21415 : p300 ∨ (¬ p295) ∨ p255 ∨ p288)
    (h21416 : p296 ∨ (¬ p295) ∨ p255 ∨ p288)
    (h21417 : p297 ∨ (¬ p295) ∨ p255 ∨ p288)
    (h1477 : p255 ∨ p287 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300))
    (h1548 : p291 ∨ p298)
    (h1553 : p292 ∨ p298)
    (h1558 : p293 ∨ p298)
    (h1563 : p294 ∨ p298)
    (h1453 : p255 ∨ p288 ∨ (¬ p291) ∨ (¬ p292) ∨ (¬ p293) ∨ (¬ p294) ∨ (¬ p295)) : (¬ p299) ∨ p255 ∨ p287 ∨ p288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p299 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p255) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p287) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p288) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p295 := by
    rcases h21414 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u3 q3)
  have u5 : p300 := by
    rcases h21415 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u4)
    · exact False.elim (u1 q2)
    · exact False.elim (u3 q3)
  have u6 : p296 := by
    rcases h21416 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u4)
    · exact False.elim (u1 q2)
    · exact False.elim (u3 q3)
  have u7 : p297 := by
    rcases h21417 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u4)
    · exact False.elim (u1 q2)
    · exact False.elim (u3 q3)
  have u8 : (¬ p298) := by
    rcases h1477 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u6)
    · exact False.elim (q3 u7)
    · exact q4
    · exact False.elim (q5 u0)
    · exact False.elim (q6 u5)
  have u9 : p291 := by
    rcases h1548 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u10 : p292 := by
    rcases h1553 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u11 : p293 := by
    rcases h1558 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u12 : p294 := by
    rcases h1563 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h1453 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u12)
  · exact False.elim (q6 u4)

theorem step21419 (p255 p287 p288 p291 p292 p293 p294 p295 p299 : Prop)
    (h21418 : (¬ p299) ∨ p255 ∨ p287 ∨ p288)
    (h1549 : p291 ∨ p299)
    (h1554 : p292 ∨ p299)
    (h1559 : p293 ∨ p299)
    (h1564 : p294 ∨ p299)
    (h1569 : p295 ∨ p299)
    (h1453 : p255 ∨ p288 ∨ (¬ p291) ∨ (¬ p292) ∨ (¬ p293) ∨ (¬ p294) ∨ (¬ p295)) : p255 ∨ p287 ∨ p288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p255) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p287) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p288) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : (¬ p299) := by
    rcases h21418 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u4 : p291 := by
    rcases h1549 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u5 : p292 := by
    rcases h1554 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p293 := by
    rcases h1559 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p294 := by
    rcases h1564 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p295 := by
    rcases h1569 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h1453 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u8)

theorem step21420 (p17 p266 p269 p270 p271 p272 p273 p277 : Prop)
    (h1416 : p269 ∨ p277)
    (h1421 : p270 ∨ p277)
    (h1426 : p271 ∨ p277)
    (h1431 : p272 ∨ p277)
    (h1436 : p273 ∨ p277)
    (h1324 : p17 ∨ p266 ∨ (¬ p269) ∨ (¬ p270) ∨ (¬ p271) ∨ (¬ p272) ∨ (¬ p273)) : p277 ∨ p266 ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p277) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p266) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p269 := by
    rcases h1416 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p270 := by
    rcases h1421 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p271 := by
    rcases h1426 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p272 := by
    rcases h1431 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p273 := by
    rcases h1436 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1324 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21421 (p17 p266 p269 p270 p271 p272 p273 p278 : Prop)
    (h1417 : p269 ∨ p278)
    (h1422 : p270 ∨ p278)
    (h1427 : p271 ∨ p278)
    (h1432 : p272 ∨ p278)
    (h1437 : p273 ∨ p278)
    (h1324 : p17 ∨ p266 ∨ (¬ p269) ∨ (¬ p270) ∨ (¬ p271) ∨ (¬ p272) ∨ (¬ p273)) : p278 ∨ p266 ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p278) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p266) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p269 := by
    rcases h1417 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p270 := by
    rcases h1422 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p271 := by
    rcases h1427 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p272 := by
    rcases h1432 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p273 := by
    rcases h1437 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1324 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21422 (p17 p266 p269 p270 p271 p272 p273 p274 : Prop)
    (h1413 : p269 ∨ p274)
    (h1418 : p270 ∨ p274)
    (h1423 : p271 ∨ p274)
    (h1428 : p272 ∨ p274)
    (h1433 : p273 ∨ p274)
    (h1324 : p17 ∨ p266 ∨ (¬ p269) ∨ (¬ p270) ∨ (¬ p271) ∨ (¬ p272) ∨ (¬ p273)) : p274 ∨ p266 ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p274) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p266) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p269 := by
    rcases h1413 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p270 := by
    rcases h1418 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p271 := by
    rcases h1423 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p272 := by
    rcases h1428 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p273 := by
    rcases h1433 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1324 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21423 (p17 p266 p269 p270 p271 p272 p273 p275 : Prop)
    (h1414 : p269 ∨ p275)
    (h1419 : p270 ∨ p275)
    (h1424 : p271 ∨ p275)
    (h1429 : p272 ∨ p275)
    (h1434 : p273 ∨ p275)
    (h1324 : p17 ∨ p266 ∨ (¬ p269) ∨ (¬ p270) ∨ (¬ p271) ∨ (¬ p272) ∨ (¬ p273)) : p275 ∨ p266 ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p275) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p266) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p269 := by
    rcases h1414 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p270 := by
    rcases h1419 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p271 := by
    rcases h1424 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p272 := by
    rcases h1429 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p273 := by
    rcases h1434 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1324 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21424 (p17 p266 p269 p270 p271 p272 p273 p274 p275 p276 p277 p278 : Prop)
    (h1349 : p17 ∨ p266 ∨ (¬ p274) ∨ (¬ p275) ∨ (¬ p276) ∨ (¬ p277) ∨ (¬ p278))
    (h1415 : p269 ∨ p276)
    (h1420 : p270 ∨ p276)
    (h1425 : p271 ∨ p276)
    (h1430 : p272 ∨ p276)
    (h1435 : p273 ∨ p276)
    (h1324 : p17 ∨ p266 ∨ (¬ p269) ∨ (¬ p270) ∨ (¬ p271) ∨ (¬ p272) ∨ (¬ p273)) : (¬ p275) ∨ p266 ∨ p17 ∨ (¬ p274) ∨ (¬ p277) ∨ (¬ p278) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p275 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p266) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p274 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p277 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p278 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p276) := by
    rcases h1349 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u0)
    · exact q4
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u5)
  have u7 : p269 := by
    rcases h1415 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p270 := by
    rcases h1420 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p271 := by
    rcases h1425 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p272 := by
    rcases h1430 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p273 := by
    rcases h1435 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h1324 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21425 (p17 p266 p274 p275 p277 p278 : Prop)
    (h21420 : p277 ∨ p266 ∨ p17)
    (h21421 : p278 ∨ p266 ∨ p17)
    (h21422 : p274 ∨ p266 ∨ p17)
    (h21423 : p275 ∨ p266 ∨ p17)
    (h21424 : (¬ p275) ∨ p266 ∨ p17 ∨ (¬ p274) ∨ (¬ p277) ∨ (¬ p278)) : p266 ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p266) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr hu)
  have u2 : p277 := by
    rcases h21420 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p278 := by
    rcases h21421 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p274 := by
    rcases h21422 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p275 := by
    rcases h21423 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21424 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21426 (p17 p124 p237 p255 p256 p266 p287 p288 : Prop)
    (h10652 : (¬ p17) ∨ (¬ p256))
    (h21425 : p266 ∨ p17)
    (h13249 : p237 ∨ (¬ p256) ∨ (¬ p287))
    (h9407 : (¬ p124) ∨ p237 ∨ (¬ p255) ∨ (¬ p266))
    (h21419 : p255 ∨ p287 ∨ p288) : p237 ∨ p288 ∨ (¬ p124) ∨ (¬ p256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p237) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p288) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p17) := by
    rcases h10652 with q0 | q1
    · exact q0
    · exact False.elim (q1 u3)
  have u5 : p266 := by
    rcases h21425 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u6 : (¬ p287) := by
    rcases h13249 with q0 | q1 | q2
    · exact False.elim (u0 q0)
    · exact False.elim (q1 u3)
    · exact q2
  have u7 : (¬ p255) := by
    rcases h9407 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u2)
    · exact False.elim (u0 q1)
    · exact q2
    · exact False.elim (q3 u5)
  rcases h21419 with q0 | q1 | q2
  · exact False.elim (u7 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (u1 q2)

theorem step21427 (p165 p169 p173 p174 p175 p176 p177 p182 : Prop)
    (h894 : p173 ∨ p182)
    (h899 : p174 ∨ p182)
    (h904 : p175 ∨ p182)
    (h909 : p176 ∨ p182)
    (h914 : p177 ∨ p182)
    (h790 : p165 ∨ p169 ∨ (¬ p173) ∨ (¬ p174) ∨ (¬ p175) ∨ (¬ p176) ∨ (¬ p177)) : p182 ∨ p165 ∨ p169 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p182) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p165) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p169) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p173 := by
    rcases h894 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p174 := by
    rcases h899 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p175 := by
    rcases h904 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p176 := by
    rcases h909 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p177 := by
    rcases h914 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h790 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21428 (p165 p169 p173 p174 p175 p176 p177 p178 : Prop)
    (h890 : p173 ∨ p178)
    (h895 : p174 ∨ p178)
    (h900 : p175 ∨ p178)
    (h905 : p176 ∨ p178)
    (h910 : p177 ∨ p178)
    (h790 : p165 ∨ p169 ∨ (¬ p173) ∨ (¬ p174) ∨ (¬ p175) ∨ (¬ p176) ∨ (¬ p177)) : p178 ∨ p165 ∨ p169 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p178) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p165) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p169) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p173 := by
    rcases h890 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p174 := by
    rcases h895 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p175 := by
    rcases h900 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p176 := by
    rcases h905 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p177 := by
    rcases h910 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h790 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21429 (p165 p169 p173 p174 p175 p176 p177 p179 : Prop)
    (h891 : p173 ∨ p179)
    (h896 : p174 ∨ p179)
    (h901 : p175 ∨ p179)
    (h906 : p176 ∨ p179)
    (h911 : p177 ∨ p179)
    (h790 : p165 ∨ p169 ∨ (¬ p173) ∨ (¬ p174) ∨ (¬ p175) ∨ (¬ p176) ∨ (¬ p177)) : p179 ∨ p165 ∨ p169 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p179) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p165) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p169) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p173 := by
    rcases h891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p174 := by
    rcases h896 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p175 := by
    rcases h901 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p176 := by
    rcases h906 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p177 := by
    rcases h911 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h790 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21430 (p165 p169 p173 p174 p175 p176 p177 p180 : Prop)
    (h892 : p173 ∨ p180)
    (h897 : p174 ∨ p180)
    (h902 : p175 ∨ p180)
    (h907 : p176 ∨ p180)
    (h912 : p177 ∨ p180)
    (h790 : p165 ∨ p169 ∨ (¬ p173) ∨ (¬ p174) ∨ (¬ p175) ∨ (¬ p176) ∨ (¬ p177)) : p180 ∨ p165 ∨ p169 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p180) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p165) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p169) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p173 := by
    rcases h892 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p174 := by
    rcases h897 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p175 := by
    rcases h902 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p176 := by
    rcases h907 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p177 := by
    rcases h912 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h790 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21431 (p3 p163 p165 p169 p173 p174 p175 p176 p177 p178 p179 p180 p181 p182 p188 p193 p237 : Prop)
    (h12250 : p3 ∨ (¬ p169) ∨ (¬ p188) ∨ (¬ p237))
    (h11977 : (¬ p165) ∨ p193 ∨ (¬ p237))
    (h21427 : p182 ∨ p165 ∨ p169)
    (h21428 : p178 ∨ p165 ∨ p169)
    (h21429 : p179 ∨ p165 ∨ p169)
    (h21430 : p180 ∨ p165 ∨ p169)
    (h817 : p163 ∨ p165 ∨ (¬ p178) ∨ (¬ p179) ∨ (¬ p180) ∨ (¬ p181) ∨ (¬ p182))
    (h893 : p173 ∨ p181)
    (h898 : p174 ∨ p181)
    (h903 : p175 ∨ p181)
    (h908 : p176 ∨ p181)
    (h913 : p177 ∨ p181)
    (h790 : p165 ∨ p169 ∨ (¬ p173) ∨ (¬ p174) ∨ (¬ p175) ∨ (¬ p176) ∨ (¬ p177)) : (¬ p237) ∨ (¬ p188) ∨ p163 ∨ p3 ∨ p193 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p193) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p169) := by
    rcases h12250 with q0 | q1 | q2 | q3
    · exact False.elim (u3 q0)
    · exact q1
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u0)
  have u6 : (¬ p165) := by
    rcases h11977 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u4 q1)
    · exact False.elim (q2 u0)
  have u7 : p182 := by
    rcases h21427 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u6 q1)
    · exact False.elim (u5 q2)
  have u8 : p178 := by
    rcases h21428 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u6 q1)
    · exact False.elim (u5 q2)
  have u9 : p179 := by
    rcases h21429 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u6 q1)
    · exact False.elim (u5 q2)
  have u10 : p180 := by
    rcases h21430 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u6 q1)
    · exact False.elim (u5 q2)
  have u11 : (¬ p181) := by
    rcases h817 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u6 q1)
    · exact False.elim (q2 u8)
    · exact False.elim (q3 u9)
    · exact False.elim (q4 u10)
    · exact q5
    · exact False.elim (q6 u7)
  have u12 : p173 := by
    rcases h893 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  have u13 : p174 := by
    rcases h898 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  have u14 : p175 := by
    rcases h903 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  have u15 : p176 := by
    rcases h908 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  have u16 : p177 := by
    rcases h913 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  rcases h790 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u12)
  · exact False.elim (q3 u13)
  · exact False.elim (q4 u14)
  · exact False.elim (q5 u15)
  · exact False.elim (q6 u16)

theorem step21432 (p258 p287 p291 p296 p297 p298 p299 p300 : Prop)
    (h21407 : p299 ∨ p258 ∨ p287)
    (h1546 : p291 ∨ p296)
    (h1547 : p291 ∨ p297)
    (h1548 : p291 ∨ p298)
    (h1550 : p291 ∨ p300)
    (h1482 : p258 ∨ p287 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300)) : p291 ∨ p258 ∨ p287 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p291) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p258) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p287) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p299 := by
    rcases h21407 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p296 := by
    rcases h1546 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p297 := by
    rcases h1547 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p298 := by
    rcases h1548 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p300 := by
    rcases h1550 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1482 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step21433 (p258 p287 p292 p296 p297 p298 p299 p300 : Prop)
    (h21407 : p299 ∨ p258 ∨ p287)
    (h1551 : p292 ∨ p296)
    (h1552 : p292 ∨ p297)
    (h1553 : p292 ∨ p298)
    (h1555 : p292 ∨ p300)
    (h1482 : p258 ∨ p287 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300)) : p292 ∨ p258 ∨ p287 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p292) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p258) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p287) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p299 := by
    rcases h21407 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p296 := by
    rcases h1551 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p297 := by
    rcases h1552 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p298 := by
    rcases h1553 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p300 := by
    rcases h1555 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1482 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step21434 (p258 p287 p293 p296 p297 p298 p299 p300 : Prop)
    (h21407 : p299 ∨ p258 ∨ p287)
    (h1556 : p293 ∨ p296)
    (h1557 : p293 ∨ p297)
    (h1558 : p293 ∨ p298)
    (h1560 : p293 ∨ p300)
    (h1482 : p258 ∨ p287 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300)) : p293 ∨ p258 ∨ p287 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p293) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p258) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p287) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p299 := by
    rcases h21407 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p296 := by
    rcases h1556 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p297 := by
    rcases h1557 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p298 := by
    rcases h1558 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p300 := by
    rcases h1560 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1482 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step21435 (p258 p287 p294 p296 p297 p298 p299 p300 : Prop)
    (h21407 : p299 ∨ p258 ∨ p287)
    (h1561 : p294 ∨ p296)
    (h1562 : p294 ∨ p297)
    (h1563 : p294 ∨ p298)
    (h1565 : p294 ∨ p300)
    (h1482 : p258 ∨ p287 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300)) : p294 ∨ p258 ∨ p287 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p294) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p258) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p287) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p299 := by
    rcases h21407 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p296 := by
    rcases h1561 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p297 := by
    rcases h1562 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p298 := by
    rcases h1563 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p300 := by
    rcases h1565 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1482 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step21436 (p258 p287 p291 p292 p293 p294 p295 p296 p297 p298 p299 p300 : Prop)
    (h21407 : p299 ∨ p258 ∨ p287)
    (h21432 : p291 ∨ p258 ∨ p287)
    (h21433 : p292 ∨ p258 ∨ p287)
    (h21434 : p293 ∨ p258 ∨ p287)
    (h21435 : p294 ∨ p258 ∨ p287)
    (h1457 : p258 ∨ p287 ∨ (¬ p291) ∨ (¬ p292) ∨ (¬ p293) ∨ (¬ p294) ∨ (¬ p295))
    (h1566 : p295 ∨ p296)
    (h1567 : p295 ∨ p297)
    (h1568 : p295 ∨ p298)
    (h1570 : p295 ∨ p300)
    (h1482 : p258 ∨ p287 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300)) : p258 ∨ p287 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p258) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p287) := fun hu => hn (Or.inr hu)
  have u2 : p299 := by
    rcases h21407 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p291 := by
    rcases h21432 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p292 := by
    rcases h21433 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p293 := by
    rcases h21434 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p294 := by
    rcases h21435 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p295) := by
    rcases h1457 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u0 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p296 := by
    rcases h1566 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p297 := by
    rcases h1567 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p298 := by
    rcases h1568 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p300 := by
    rcases h1570 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h1482 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u11)

theorem step21437 (p41 p44 p55 p56 p57 p58 p59 p60 : Prop)
    (h253 : p55 ∨ p56)
    (h254 : p55 ∨ p57)
    (h255 : p55 ∨ p58)
    (h256 : p55 ∨ p59)
    (h165 : p41 ∨ p44 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60)) : p55 ∨ (¬ p60) ∨ p44 ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p55) := fun hu => hn (Or.inl hu)
  have u1 : p60 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p44) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p56 := by
    rcases h253 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p57 := by
    rcases h254 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p58 := by
    rcases h255 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p59 := by
    rcases h256 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h165 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21438 (p41 p45 p51 p52 p53 p54 p55 p56 : Prop)
    (h233 : p51 ∨ p56)
    (h238 : p52 ∨ p56)
    (h243 : p53 ∨ p56)
    (h248 : p54 ∨ p56)
    (h145 : p41 ∨ p45 ∨ (¬ p51) ∨ (¬ p52) ∨ (¬ p53) ∨ (¬ p54) ∨ (¬ p55)) : p56 ∨ (¬ p55) ∨ p41 ∨ p45 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p56) := fun hu => hn (Or.inl hu)
  have u1 : p55 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p45) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p51 := by
    rcases h233 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p52 := by
    rcases h238 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p53 := by
    rcases h243 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p54 := by
    rcases h248 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h145 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21439 (p41 p45 p51 p52 p53 p54 p55 p57 : Prop)
    (h234 : p51 ∨ p57)
    (h239 : p52 ∨ p57)
    (h244 : p53 ∨ p57)
    (h249 : p54 ∨ p57)
    (h145 : p41 ∨ p45 ∨ (¬ p51) ∨ (¬ p52) ∨ (¬ p53) ∨ (¬ p54) ∨ (¬ p55)) : p57 ∨ (¬ p55) ∨ p41 ∨ p45 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p57) := fun hu => hn (Or.inl hu)
  have u1 : p55 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p45) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p51 := by
    rcases h234 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p52 := by
    rcases h239 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p53 := by
    rcases h244 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p54 := by
    rcases h249 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h145 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21440 (p41 p45 p51 p52 p53 p54 p55 p58 : Prop)
    (h235 : p51 ∨ p58)
    (h240 : p52 ∨ p58)
    (h245 : p53 ∨ p58)
    (h250 : p54 ∨ p58)
    (h145 : p41 ∨ p45 ∨ (¬ p51) ∨ (¬ p52) ∨ (¬ p53) ∨ (¬ p54) ∨ (¬ p55)) : p58 ∨ (¬ p55) ∨ p41 ∨ p45 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p58) := fun hu => hn (Or.inl hu)
  have u1 : p55 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p45) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p51 := by
    rcases h235 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p52 := by
    rcases h240 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p53 := by
    rcases h245 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p54 := by
    rcases h250 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h145 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21442 (p41 p45 p51 p52 p53 p54 p55 p60 : Prop)
    (h237 : p51 ∨ p60)
    (h242 : p52 ∨ p60)
    (h247 : p53 ∨ p60)
    (h252 : p54 ∨ p60)
    (h257 : p55 ∨ p60)
    (h145 : p41 ∨ p45 ∨ (¬ p51) ∨ (¬ p52) ∨ (¬ p53) ∨ (¬ p54) ∨ (¬ p55)) : p60 ∨ p41 ∨ p45 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p60) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p41) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p45) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p51 := by
    rcases h237 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p52 := by
    rcases h242 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p53 := by
    rcases h247 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p54 := by
    rcases h252 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p55 := by
    rcases h257 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h145 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21443 (p41 p45 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 : Prop)
    (h21442 : p60 ∨ p41 ∨ p45)
    (h21438 : p56 ∨ (¬ p55) ∨ p41 ∨ p45)
    (h21439 : p57 ∨ (¬ p55) ∨ p41 ∨ p45)
    (h21440 : p58 ∨ (¬ p55) ∨ p41 ∨ p45)
    (h170 : p41 ∨ p45 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60))
    (h236 : p51 ∨ p59)
    (h241 : p52 ∨ p59)
    (h246 : p53 ∨ p59)
    (h251 : p54 ∨ p59)
    (h145 : p41 ∨ p45 ∨ (¬ p51) ∨ (¬ p52) ∨ (¬ p53) ∨ (¬ p54) ∨ (¬ p55)) : (¬ p55) ∨ p41 ∨ p45 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p55 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p41) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p45) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p60 := by
    rcases h21442 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p56 := by
    rcases h21438 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u5 : p57 := by
    rcases h21439 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u6 : p58 := by
    rcases h21440 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u7 : (¬ p59) := by
    rcases h170 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u6)
    · exact q5
    · exact False.elim (q6 u3)
  have u8 : p51 := by
    rcases h236 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p52 := by
    rcases h241 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p53 := by
    rcases h246 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p54 := by
    rcases h251 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h145 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u0)

theorem step21444 (p41 p45 p55 p56 p57 p58 p59 p60 : Prop)
    (h21442 : p60 ∨ p41 ∨ p45)
    (h21443 : (¬ p55) ∨ p41 ∨ p45)
    (h253 : p55 ∨ p56)
    (h254 : p55 ∨ p57)
    (h255 : p55 ∨ p58)
    (h256 : p55 ∨ p59)
    (h170 : p41 ∨ p45 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60)) : p41 ∨ p45 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p41) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p45) := fun hu => hn (Or.inr hu)
  have u2 : p60 := by
    rcases h21442 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : (¬ p55) := by
    rcases h21443 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p56 := by
    rcases h253 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  have u5 : p57 := by
    rcases h254 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  have u6 : p58 := by
    rcases h255 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  have u7 : p59 := by
    rcases h256 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  rcases h170 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u2)

theorem step21446 (p126 p514 p522 p527 p528 p529 p530 p531 : Prop)
    (h2959 : p522 ∨ p527)
    (h2960 : p522 ∨ p528)
    (h2961 : p522 ∨ p529)
    (h2962 : p522 ∨ p530)
    (h2886 : p126 ∨ p514 ∨ (¬ p527) ∨ (¬ p528) ∨ (¬ p529) ∨ (¬ p530) ∨ (¬ p531)) : p522 ∨ (¬ p531) ∨ p514 ∨ p126 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p522) := fun hu => hn (Or.inl hu)
  have u1 : p531 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p514) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p126) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p527 := by
    rcases h2959 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p528 := by
    rcases h2960 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p529 := by
    rcases h2961 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p530 := by
    rcases h2962 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2886 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21447 (p126 p514 p523 p527 p528 p529 p530 p531 : Prop)
    (h2964 : p523 ∨ p527)
    (h2965 : p523 ∨ p528)
    (h2966 : p523 ∨ p529)
    (h2967 : p523 ∨ p530)
    (h2886 : p126 ∨ p514 ∨ (¬ p527) ∨ (¬ p528) ∨ (¬ p529) ∨ (¬ p530) ∨ (¬ p531)) : p523 ∨ (¬ p531) ∨ p514 ∨ p126 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p523) := fun hu => hn (Or.inl hu)
  have u1 : p531 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p514) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p126) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p527 := by
    rcases h2964 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p528 := by
    rcases h2965 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p529 := by
    rcases h2966 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p530 := by
    rcases h2967 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2886 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21448 (p126 p514 p524 p527 p528 p529 p530 p531 : Prop)
    (h2969 : p524 ∨ p527)
    (h2970 : p524 ∨ p528)
    (h2971 : p524 ∨ p529)
    (h2972 : p524 ∨ p530)
    (h2886 : p126 ∨ p514 ∨ (¬ p527) ∨ (¬ p528) ∨ (¬ p529) ∨ (¬ p530) ∨ (¬ p531)) : p524 ∨ (¬ p531) ∨ p514 ∨ p126 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p524) := fun hu => hn (Or.inl hu)
  have u1 : p531 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p514) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p126) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p527 := by
    rcases h2969 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p528 := by
    rcases h2970 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p529 := by
    rcases h2971 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p530 := by
    rcases h2972 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2886 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21449 (p345 p350 p356 p357 p358 p359 p360 p361 : Prop)
    (h1945 : p356 ∨ p357)
    (h1946 : p356 ∨ p358)
    (h1947 : p356 ∨ p359)
    (h1948 : p356 ∨ p360)
    (h1853 : p345 ∨ p350 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361)) : p356 ∨ (¬ p361) ∨ p350 ∨ p345 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p356) := fun hu => hn (Or.inl hu)
  have u1 : p361 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p350) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p345) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h1853 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21450 (p346 p350 p352 p353 p354 p355 p356 p357 : Prop)
    (h1925 : p352 ∨ p357)
    (h1930 : p353 ∨ p357)
    (h1935 : p354 ∨ p357)
    (h1940 : p355 ∨ p357)
    (h1838 : p346 ∨ p350 ∨ (¬ p352) ∨ (¬ p353) ∨ (¬ p354) ∨ (¬ p355) ∨ (¬ p356)) : p357 ∨ (¬ p356) ∨ p346 ∨ p350 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p357) := fun hu => hn (Or.inl hu)
  have u1 : p356 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p346) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p350) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h1838 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21451 (p346 p350 p352 p353 p354 p355 p356 p358 : Prop)
    (h1926 : p352 ∨ p358)
    (h1931 : p353 ∨ p358)
    (h1936 : p354 ∨ p358)
    (h1941 : p355 ∨ p358)
    (h1838 : p346 ∨ p350 ∨ (¬ p352) ∨ (¬ p353) ∨ (¬ p354) ∨ (¬ p355) ∨ (¬ p356)) : p358 ∨ (¬ p356) ∨ p346 ∨ p350 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p358) := fun hu => hn (Or.inl hu)
  have u1 : p356 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p346) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p350) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h1838 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21452 (p346 p350 p352 p353 p354 p355 p356 p359 : Prop)
    (h1927 : p352 ∨ p359)
    (h1932 : p353 ∨ p359)
    (h1937 : p354 ∨ p359)
    (h1942 : p355 ∨ p359)
    (h1838 : p346 ∨ p350 ∨ (¬ p352) ∨ (¬ p353) ∨ (¬ p354) ∨ (¬ p355) ∨ (¬ p356)) : p359 ∨ (¬ p356) ∨ p346 ∨ p350 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p359) := fun hu => hn (Or.inl hu)
  have u1 : p356 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p346) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p350) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h1838 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21453 (p344 p345 p346 p350 p352 p353 p354 p355 p356 p357 p358 p359 p360 p361 : Prop)
    (h21358 : p345 ∨ p344)
    (h7033 : (¬ p344) ∨ (¬ p346))
    (h21449 : p356 ∨ (¬ p361) ∨ p350 ∨ p345)
    (h21450 : p357 ∨ (¬ p356) ∨ p346 ∨ p350)
    (h21451 : p358 ∨ (¬ p356) ∨ p346 ∨ p350)
    (h21452 : p359 ∨ (¬ p356) ∨ p346 ∨ p350)
    (h1853 : p345 ∨ p350 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361))
    (h1928 : p352 ∨ p360)
    (h1933 : p353 ∨ p360)
    (h1938 : p354 ∨ p360)
    (h1943 : p355 ∨ p360)
    (h1838 : p346 ∨ p350 ∨ (¬ p352) ∨ (¬ p353) ∨ (¬ p354) ∨ (¬ p355) ∨ (¬ p356)) : (¬ p361) ∨ p350 ∨ p345 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p361 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p350) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p345) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p344 := by
    rcases h21358 with q0 | q1
    · exact False.elim (u2 q0)
    · exact q1
  have u4 : (¬ p346) := by
    rcases h7033 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  have u5 : p356 := by
    rcases h21449 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u6 : p357 := by
    rcases h21450 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u5)
    · exact False.elim (u4 q2)
    · exact False.elim (u1 q3)
  have u7 : p358 := by
    rcases h21451 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u5)
    · exact False.elim (u4 q2)
    · exact False.elim (u1 q3)
  have u8 : p359 := by
    rcases h21452 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u5)
    · exact False.elim (u4 q2)
    · exact False.elim (u1 q3)
  have u9 : (¬ p360) := by
    rcases h1853 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u6)
    · exact False.elim (q3 u7)
    · exact False.elim (q4 u8)
    · exact q5
    · exact False.elim (q6 u0)
  have u10 : p352 := by
    rcases h1928 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  have u11 : p353 := by
    rcases h1933 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  have u12 : p354 := by
    rcases h1938 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  have u13 : p355 := by
    rcases h1943 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h1838 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u12)
  · exact False.elim (q5 u13)
  · exact False.elim (q6 u5)

theorem step21454 (p126 p185 p237 p255 p256 p258 p287 p288 p344 p345 p346 p350 p352 p353 p354 p355 p356 p361 : Prop)
    (h13249 : p237 ∨ (¬ p256) ∨ (¬ p287))
    (h21233 : p237 ∨ p185)
    (h21436 : p258 ∨ p287)
    (h9406 : (¬ p258) ∨ (¬ p288))
    (h9410 : (¬ p126) ∨ (¬ p258) ∨ (¬ p345))
    (h21419 : p255 ∨ p287 ∨ p288)
    (h21358 : p345 ∨ p344)
    (h19175 : (¬ p126) ∨ (¬ p185) ∨ (¬ p255) ∨ (¬ p256) ∨ (¬ p350))
    (h7033 : (¬ p344) ∨ (¬ p346))
    (h21453 : (¬ p361) ∨ p350 ∨ p345)
    (h1929 : p352 ∨ p361)
    (h1934 : p353 ∨ p361)
    (h1939 : p354 ∨ p361)
    (h1944 : p355 ∨ p361)
    (h1949 : p356 ∨ p361)
    (h1838 : p346 ∨ p350 ∨ (¬ p352) ∨ (¬ p353) ∨ (¬ p354) ∨ (¬ p355) ∨ (¬ p356)) : p237 ∨ (¬ p256) ∨ (¬ p126) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p237) := fun hu => hn (Or.inl hu)
  have u1 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p287) := by
    rcases h13249 with q0 | q1 | q2
    · exact False.elim (u0 q0)
    · exact False.elim (q1 u1)
    · exact q2
  have u4 : p185 := by
    rcases h21233 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p258 := by
    rcases h21436 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : (¬ p288) := by
    rcases h9406 with q0 | q1
    · exact False.elim (q0 u5)
    · exact q1
  have u7 : (¬ p345) := by
    rcases h9410 with q0 | q1 | q2
    · exact False.elim (q0 u2)
    · exact False.elim (q1 u5)
    · exact q2
  have u8 : p255 := by
    rcases h21419 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u3 q1)
    · exact False.elim (u6 q2)
  have u9 : p344 := by
    rcases h21358 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : (¬ p350) := by
    rcases h19175 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u2)
    · exact False.elim (q1 u4)
    · exact False.elim (q2 u8)
    · exact False.elim (q3 u1)
    · exact q4
  have u11 : (¬ p346) := by
    rcases h7033 with q0 | q1
    · exact False.elim (q0 u9)
    · exact q1
  have u12 : (¬ p361) := by
    rcases h21453 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u10 q1)
    · exact False.elim (u7 q2)
  have u13 : p352 := by
    rcases h1929 with q0 | q1
    · exact q0
    · exact False.elim (u12 q1)
  have u14 : p353 := by
    rcases h1934 with q0 | q1
    · exact q0
    · exact False.elim (u12 q1)
  have u15 : p354 := by
    rcases h1939 with q0 | q1
    · exact q0
    · exact False.elim (u12 q1)
  have u16 : p355 := by
    rcases h1944 with q0 | q1
    · exact q0
    · exact False.elim (u12 q1)
  have u17 : p356 := by
    rcases h1949 with q0 | q1
    · exact q0
    · exact False.elim (u12 q1)
  rcases h1838 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u11 q0)
  · exact False.elim (u10 q1)
  · exact False.elim (q2 u13)
  · exact False.elim (q3 u14)
  · exact False.elim (q4 u15)
  · exact False.elim (q5 u16)
  · exact False.elim (q6 u17)

theorem step21455 (p1328 p1333 p1336 p1337 p1338 p1339 p1340 p1344 : Prop)
    (h8075 : p1336 ∨ p1344)
    (h8080 : p1337 ∨ p1344)
    (h8085 : p1338 ∨ p1344)
    (h8090 : p1339 ∨ p1344)
    (h8095 : p1340 ∨ p1344)
    (h7974 : p1328 ∨ p1333 ∨ (¬ p1336) ∨ (¬ p1337) ∨ (¬ p1338) ∨ (¬ p1339) ∨ (¬ p1340)) : p1344 ∨ p1328 ∨ p1333 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1344) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1328) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1333) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1336 := by
    rcases h8075 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1337 := by
    rcases h8080 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1338 := by
    rcases h8085 with q0 | q1
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
  rcases h7974 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21456 (p1328 p1333 p1336 p1337 p1338 p1339 p1340 p1345 : Prop)
    (h8076 : p1336 ∨ p1345)
    (h8081 : p1337 ∨ p1345)
    (h8086 : p1338 ∨ p1345)
    (h8091 : p1339 ∨ p1345)
    (h8096 : p1340 ∨ p1345)
    (h7974 : p1328 ∨ p1333 ∨ (¬ p1336) ∨ (¬ p1337) ∨ (¬ p1338) ∨ (¬ p1339) ∨ (¬ p1340)) : p1345 ∨ p1328 ∨ p1333 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1345) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1328) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1333) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1336 := by
    rcases h8076 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1337 := by
    rcases h8081 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1338 := by
    rcases h8086 with q0 | q1
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
  rcases h7974 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21457 (p1328 p1333 p1336 p1337 p1338 p1339 p1340 p1341 : Prop)
    (h8072 : p1336 ∨ p1341)
    (h8077 : p1337 ∨ p1341)
    (h8082 : p1338 ∨ p1341)
    (h8087 : p1339 ∨ p1341)
    (h8092 : p1340 ∨ p1341)
    (h7974 : p1328 ∨ p1333 ∨ (¬ p1336) ∨ (¬ p1337) ∨ (¬ p1338) ∨ (¬ p1339) ∨ (¬ p1340)) : p1341 ∨ p1328 ∨ p1333 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1341) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1328) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1333) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1336 := by
    rcases h8072 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1337 := by
    rcases h8077 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1338 := by
    rcases h8082 with q0 | q1
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
  rcases h7974 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21458 (p1328 p1333 p1336 p1337 p1338 p1339 p1340 p1342 : Prop)
    (h8073 : p1336 ∨ p1342)
    (h8078 : p1337 ∨ p1342)
    (h8083 : p1338 ∨ p1342)
    (h8088 : p1339 ∨ p1342)
    (h8093 : p1340 ∨ p1342)
    (h7974 : p1328 ∨ p1333 ∨ (¬ p1336) ∨ (¬ p1337) ∨ (¬ p1338) ∨ (¬ p1339) ∨ (¬ p1340)) : p1342 ∨ p1328 ∨ p1333 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1342) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1328) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1333) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1336 := by
    rcases h8073 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1337 := by
    rcases h8078 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1338 := by
    rcases h8083 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1339 := by
    rcases h8088 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1340 := by
    rcases h8093 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7974 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21459 (p1328 p1333 p1336 p1337 p1338 p1339 p1340 p1341 p1342 p1343 p1344 p1345 : Prop)
    (h7999 : p1328 ∨ p1333 ∨ (¬ p1341) ∨ (¬ p1342) ∨ (¬ p1343) ∨ (¬ p1344) ∨ (¬ p1345))
    (h8074 : p1336 ∨ p1343)
    (h8079 : p1337 ∨ p1343)
    (h8084 : p1338 ∨ p1343)
    (h8089 : p1339 ∨ p1343)
    (h8094 : p1340 ∨ p1343)
    (h7974 : p1328 ∨ p1333 ∨ (¬ p1336) ∨ (¬ p1337) ∨ (¬ p1338) ∨ (¬ p1339) ∨ (¬ p1340)) : (¬ p1342) ∨ (¬ p1344) ∨ p1333 ∨ p1328 ∨ (¬ p1341) ∨ (¬ p1345) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1342 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1333) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1328) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1341 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1345 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1343) := by
    rcases h7999 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u0)
    · exact q4
    · exact False.elim (q5 u1)
    · exact False.elim (q6 u5)
  have u7 : p1336 := by
    rcases h8074 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1337 := by
    rcases h8079 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1338 := by
    rcases h8084 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1339 := by
    rcases h8089 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1340 := by
    rcases h8094 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h7974 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21460 (p1328 p1333 p1341 p1342 p1344 p1345 : Prop)
    (h21455 : p1344 ∨ p1328 ∨ p1333)
    (h21456 : p1345 ∨ p1328 ∨ p1333)
    (h21457 : p1341 ∨ p1328 ∨ p1333)
    (h21458 : p1342 ∨ p1328 ∨ p1333)
    (h21459 : (¬ p1342) ∨ (¬ p1344) ∨ p1333 ∨ p1328 ∨ (¬ p1341) ∨ (¬ p1345)) : p1328 ∨ p1333 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1328) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1333) := fun hu => hn (Or.inr hu)
  have u2 : p1344 := by
    rcases h21455 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1345 := by
    rcases h21456 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1341 := by
    rcases h21457 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1342 := by
    rcases h21458 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21459 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step21461 (p918 p926 p930 p931 p932 p933 p934 p935 : Prop)
    (h5433 : p930 ∨ p935)
    (h5438 : p931 ∨ p935)
    (h5443 : p932 ∨ p935)
    (h5448 : p933 ∨ p935)
    (h5453 : p934 ∨ p935)
    (h5343 : p918 ∨ p926 ∨ (¬ p930) ∨ (¬ p931) ∨ (¬ p932) ∨ (¬ p933) ∨ (¬ p934)) : p935 ∨ p918 ∨ p926 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p935) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p926) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p930 := by
    rcases h5433 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p931 := by
    rcases h5438 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p932 := by
    rcases h5443 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p933 := by
    rcases h5448 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p934 := by
    rcases h5453 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5343 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21462 (p918 p926 p930 p931 p932 p933 p934 p936 : Prop)
    (h5434 : p930 ∨ p936)
    (h5439 : p931 ∨ p936)
    (h5444 : p932 ∨ p936)
    (h5449 : p933 ∨ p936)
    (h5454 : p934 ∨ p936)
    (h5343 : p918 ∨ p926 ∨ (¬ p930) ∨ (¬ p931) ∨ (¬ p932) ∨ (¬ p933) ∨ (¬ p934)) : p936 ∨ p918 ∨ p926 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p936) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p926) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p930 := by
    rcases h5434 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p931 := by
    rcases h5439 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p932 := by
    rcases h5444 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p933 := by
    rcases h5449 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p934 := by
    rcases h5454 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5343 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21463 (p918 p926 p930 p931 p932 p933 p934 p937 : Prop)
    (h5435 : p930 ∨ p937)
    (h5440 : p931 ∨ p937)
    (h5445 : p932 ∨ p937)
    (h5450 : p933 ∨ p937)
    (h5455 : p934 ∨ p937)
    (h5343 : p918 ∨ p926 ∨ (¬ p930) ∨ (¬ p931) ∨ (¬ p932) ∨ (¬ p933) ∨ (¬ p934)) : p937 ∨ p918 ∨ p926 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p937) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p926) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p930 := by
    rcases h5435 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p931 := by
    rcases h5440 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p932 := by
    rcases h5445 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p933 := by
    rcases h5450 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p934 := by
    rcases h5455 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5343 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21464 (p918 p926 p930 p931 p932 p933 p934 p938 : Prop)
    (h5436 : p930 ∨ p938)
    (h5441 : p931 ∨ p938)
    (h5446 : p932 ∨ p938)
    (h5451 : p933 ∨ p938)
    (h5456 : p934 ∨ p938)
    (h5343 : p918 ∨ p926 ∨ (¬ p930) ∨ (¬ p931) ∨ (¬ p932) ∨ (¬ p933) ∨ (¬ p934)) : p938 ∨ p918 ∨ p926 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p938) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p926) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p930 := by
    rcases h5436 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p931 := by
    rcases h5441 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p932 := by
    rcases h5446 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p933 := by
    rcases h5451 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p934 := by
    rcases h5456 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5343 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21465 (p918 p922 p926 p930 p931 p932 p933 p934 p935 p936 p937 p938 p939 : Prop)
    (h21461 : p935 ∨ p918 ∨ p926)
    (h21462 : p936 ∨ p918 ∨ p926)
    (h21463 : p937 ∨ p918 ∨ p926)
    (h21464 : p938 ∨ p918 ∨ p926)
    (h5358 : p922 ∨ p926 ∨ (¬ p935) ∨ (¬ p936) ∨ (¬ p937) ∨ (¬ p938) ∨ (¬ p939))
    (h5437 : p930 ∨ p939)
    (h5442 : p931 ∨ p939)
    (h5447 : p932 ∨ p939)
    (h5452 : p933 ∨ p939)
    (h5457 : p934 ∨ p939)
    (h5343 : p918 ∨ p926 ∨ (¬ p930) ∨ (¬ p931) ∨ (¬ p932) ∨ (¬ p933) ∨ (¬ p934)) : p918 ∨ p922 ∨ p926 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p918) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p922) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p926) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p935 := by
    rcases h21461 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u4 : p936 := by
    rcases h21462 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u5 : p937 := by
    rcases h21463 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u6 : p938 := by
    rcases h21464 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u7 : (¬ p939) := by
    rcases h5358 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p930 := by
    rcases h5437 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p931 := by
    rcases h5442 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p932 := by
    rcases h5447 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p933 := by
    rcases h5452 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u12 : p934 := by
    rcases h5457 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h5343 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u12)

theorem step21466 (p574 p581 p584 p585 p586 p587 p588 p589 p590 p591 p592 p593 : Prop)
    (h3245 : p574 ∨ p581 ∨ (¬ p584) ∨ (¬ p585) ∨ (¬ p586) ∨ (¬ p587) ∨ (¬ p588))
    (h3358 : p588 ∨ p589)
    (h3359 : p588 ∨ p590)
    (h3360 : p588 ∨ p591)
    (h3361 : p588 ∨ p592)
    (h3362 : p588 ∨ p593)
    (h3270 : p574 ∨ p581 ∨ (¬ p589) ∨ (¬ p590) ∨ (¬ p591) ∨ (¬ p592) ∨ (¬ p593)) : (¬ p587) ∨ (¬ p586) ∨ p574 ∨ p581 ∨ (¬ p584) ∨ (¬ p585) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p587 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p586 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p574) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p581) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p585 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p588) := by
    rcases h3245 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p589 := by
    rcases h3358 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p590 := by
    rcases h3359 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p591 := by
    rcases h3360 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p592 := by
    rcases h3361 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p593 := by
    rcases h3362 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h3270 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21467 (p574 p581 p584 p585 p586 p587 : Prop)
    (h21330 : p584 ∨ p581 ∨ p574)
    (h21331 : p585 ∨ p581 ∨ p574)
    (h21332 : p586 ∨ p581 ∨ p574)
    (h21333 : p587 ∨ p581 ∨ p574)
    (h21466 : (¬ p587) ∨ (¬ p586) ∨ p574 ∨ p581 ∨ (¬ p584) ∨ (¬ p585)) : p581 ∨ p574 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p581) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p574) := fun hu => hn (Or.inr hu)
  have u2 : p584 := by
    rcases h21330 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p585 := by
    rcases h21331 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p586 := by
    rcases h21332 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p587 := by
    rcases h21333 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21466 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21468 (p90 p237 p840 p897 p918 p922 p926 : Prop)
    (h10259 : (¬ p840) ∨ (¬ p897) ∨ (¬ p926))
    (h19352 : (¬ p90) ∨ (¬ p237) ∨ (¬ p840) ∨ (¬ p897) ∨ (¬ p922))
    (h21465 : p918 ∨ p922 ∨ p926) : (¬ p897) ∨ p918 ∨ (¬ p90) ∨ (¬ p840) ∨ (¬ p237) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p90 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p926) := by
    rcases h10259 with q0 | q1 | q2
    · exact False.elim (q0 u3)
    · exact False.elim (q1 u0)
    · exact q2
  have u6 : (¬ p922) := by
    rcases h19352 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u2)
    · exact False.elim (q1 u4)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u0)
    · exact q4
  rcases h21465 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (u5 q2)

theorem step21469 (p918 p926 p930 p931 p932 p933 p934 p935 p936 p937 p938 p939 : Prop)
    (h5368 : p918 ∨ p926 ∨ (¬ p935) ∨ (¬ p936) ∨ (¬ p937) ∨ (¬ p938) ∨ (¬ p939))
    (h5437 : p930 ∨ p939)
    (h5442 : p931 ∨ p939)
    (h5447 : p932 ∨ p939)
    (h5452 : p933 ∨ p939)
    (h5457 : p934 ∨ p939)
    (h5343 : p918 ∨ p926 ∨ (¬ p930) ∨ (¬ p931) ∨ (¬ p932) ∨ (¬ p933) ∨ (¬ p934)) : (¬ p938) ∨ (¬ p937) ∨ p926 ∨ p918 ∨ (¬ p935) ∨ (¬ p936) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p938 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p937 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p926) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p935 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p936 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p939) := by
    rcases h5368 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p930 := by
    rcases h5437 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p931 := by
    rcases h5442 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p932 := by
    rcases h5447 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p933 := by
    rcases h5452 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p934 := by
    rcases h5457 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h5343 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21470 (p918 p926 p935 p936 p937 p938 : Prop)
    (h21461 : p935 ∨ p918 ∨ p926)
    (h21462 : p936 ∨ p918 ∨ p926)
    (h21463 : p937 ∨ p918 ∨ p926)
    (h21464 : p938 ∨ p918 ∨ p926)
    (h21469 : (¬ p938) ∨ (¬ p937) ∨ p926 ∨ p918 ∨ (¬ p935) ∨ (¬ p936)) : p926 ∨ p918 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p926) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr hu)
  have u2 : p935 := by
    rcases h21461 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u3 : p936 := by
    rcases h21462 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u4 : p937 := by
    rcases h21463 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u5 : p938 := by
    rcases h21464 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  rcases h21469 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21471 (p940 p946 p949 p950 p951 p952 p953 p958 : Prop)
    (h5564 : p949 ∨ p958)
    (h5569 : p950 ∨ p958)
    (h5574 : p951 ∨ p958)
    (h5579 : p952 ∨ p958)
    (h5584 : p953 ∨ p958)
    (h5471 : p940 ∨ p946 ∨ (¬ p949) ∨ (¬ p950) ∨ (¬ p951) ∨ (¬ p952) ∨ (¬ p953)) : p958 ∨ p946 ∨ p940 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p958) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p946) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p940) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p949 := by
    rcases h5564 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p950 := by
    rcases h5569 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p951 := by
    rcases h5574 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p952 := by
    rcases h5579 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p953 := by
    rcases h5584 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5471 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21472 (p940 p946 p949 p950 p951 p952 p953 p954 : Prop)
    (h5560 : p949 ∨ p954)
    (h5565 : p950 ∨ p954)
    (h5570 : p951 ∨ p954)
    (h5575 : p952 ∨ p954)
    (h5580 : p953 ∨ p954)
    (h5471 : p940 ∨ p946 ∨ (¬ p949) ∨ (¬ p950) ∨ (¬ p951) ∨ (¬ p952) ∨ (¬ p953)) : p954 ∨ p946 ∨ p940 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p954) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p946) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p940) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p949 := by
    rcases h5560 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p950 := by
    rcases h5565 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p951 := by
    rcases h5570 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p952 := by
    rcases h5575 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p953 := by
    rcases h5580 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5471 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21473 (p940 p946 p949 p950 p951 p952 p953 p955 : Prop)
    (h5561 : p949 ∨ p955)
    (h5566 : p950 ∨ p955)
    (h5571 : p951 ∨ p955)
    (h5576 : p952 ∨ p955)
    (h5581 : p953 ∨ p955)
    (h5471 : p940 ∨ p946 ∨ (¬ p949) ∨ (¬ p950) ∨ (¬ p951) ∨ (¬ p952) ∨ (¬ p953)) : p955 ∨ p946 ∨ p940 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p955) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p946) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p940) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p949 := by
    rcases h5561 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p950 := by
    rcases h5566 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p951 := by
    rcases h5571 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p952 := by
    rcases h5576 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p953 := by
    rcases h5581 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5471 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21474 (p940 p946 p949 p950 p951 p952 p953 p956 : Prop)
    (h5562 : p949 ∨ p956)
    (h5567 : p950 ∨ p956)
    (h5572 : p951 ∨ p956)
    (h5577 : p952 ∨ p956)
    (h5582 : p953 ∨ p956)
    (h5471 : p940 ∨ p946 ∨ (¬ p949) ∨ (¬ p950) ∨ (¬ p951) ∨ (¬ p952) ∨ (¬ p953)) : p956 ∨ p946 ∨ p940 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p956) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p946) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p940) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p949 := by
    rcases h5562 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p950 := by
    rcases h5567 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p951 := by
    rcases h5572 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p952 := by
    rcases h5577 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p953 := by
    rcases h5582 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5471 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21475 (p940 p946 p949 p950 p951 p952 p953 p954 p955 p956 p957 p958 : Prop)
    (h5496 : p940 ∨ p946 ∨ (¬ p954) ∨ (¬ p955) ∨ (¬ p956) ∨ (¬ p957) ∨ (¬ p958))
    (h5563 : p949 ∨ p957)
    (h5568 : p950 ∨ p957)
    (h5573 : p951 ∨ p957)
    (h5578 : p952 ∨ p957)
    (h5583 : p953 ∨ p957)
    (h5471 : p940 ∨ p946 ∨ (¬ p949) ∨ (¬ p950) ∨ (¬ p951) ∨ (¬ p952) ∨ (¬ p953)) : (¬ p956) ∨ p946 ∨ p940 ∨ (¬ p954) ∨ (¬ p958) ∨ (¬ p955) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p956 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p946) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p940) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p954 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p958 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p955 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p957) := by
    rcases h5496 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u0)
    · exact q5
    · exact False.elim (q6 u4)
  have u7 : p949 := by
    rcases h5563 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p950 := by
    rcases h5568 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p951 := by
    rcases h5573 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p952 := by
    rcases h5578 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p953 := by
    rcases h5583 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h5471 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21476 (p940 p946 p954 p955 p956 p958 : Prop)
    (h21471 : p958 ∨ p946 ∨ p940)
    (h21472 : p954 ∨ p946 ∨ p940)
    (h21473 : p955 ∨ p946 ∨ p940)
    (h21474 : p956 ∨ p946 ∨ p940)
    (h21475 : (¬ p956) ∨ p946 ∨ p940 ∨ (¬ p954) ∨ (¬ p958) ∨ (¬ p955)) : p946 ∨ p940 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p946) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p940) := fun hu => hn (Or.inr hu)
  have u2 : p958 := by
    rcases h21471 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p954 := by
    rcases h21472 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p955 := by
    rcases h21473 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p956 := by
    rcases h21474 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21475 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u4)

theorem step21477 (p1076 p1077 p1085 p1086 p1087 p1088 p1089 p1092 : Prop)
    (h6452 : p1085 ∨ p1092)
    (h6457 : p1086 ∨ p1092)
    (h6462 : p1087 ∨ p1092)
    (h6467 : p1088 ∨ p1092)
    (h6472 : p1089 ∨ p1092)
    (h6362 : p1076 ∨ p1077 ∨ (¬ p1085) ∨ (¬ p1086) ∨ (¬ p1087) ∨ (¬ p1088) ∨ (¬ p1089)) : p1092 ∨ p1077 ∨ p1076 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1092) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1077) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1085 := by
    rcases h6452 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1086 := by
    rcases h6457 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1087 := by
    rcases h6462 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1088 := by
    rcases h6467 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1089 := by
    rcases h6472 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6362 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21478 (p1076 p1077 p1085 p1086 p1087 p1088 p1089 p1094 : Prop)
    (h6454 : p1085 ∨ p1094)
    (h6459 : p1086 ∨ p1094)
    (h6464 : p1087 ∨ p1094)
    (h6469 : p1088 ∨ p1094)
    (h6474 : p1089 ∨ p1094)
    (h6362 : p1076 ∨ p1077 ∨ (¬ p1085) ∨ (¬ p1086) ∨ (¬ p1087) ∨ (¬ p1088) ∨ (¬ p1089)) : p1094 ∨ p1077 ∨ p1076 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1094) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1077) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1085 := by
    rcases h6454 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1086 := by
    rcases h6459 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1087 := by
    rcases h6464 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1088 := by
    rcases h6469 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1089 := by
    rcases h6474 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6362 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21479 (p1076 p1077 p1085 p1086 p1087 p1088 p1089 p1090 : Prop)
    (h6450 : p1085 ∨ p1090)
    (h6455 : p1086 ∨ p1090)
    (h6460 : p1087 ∨ p1090)
    (h6465 : p1088 ∨ p1090)
    (h6470 : p1089 ∨ p1090)
    (h6362 : p1076 ∨ p1077 ∨ (¬ p1085) ∨ (¬ p1086) ∨ (¬ p1087) ∨ (¬ p1088) ∨ (¬ p1089)) : p1090 ∨ p1077 ∨ p1076 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1090) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1077) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1085 := by
    rcases h6450 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1086 := by
    rcases h6455 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1087 := by
    rcases h6460 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1088 := by
    rcases h6465 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1089 := by
    rcases h6470 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6362 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21480 (p1076 p1077 p1085 p1086 p1087 p1088 p1089 p1091 : Prop)
    (h6451 : p1085 ∨ p1091)
    (h6456 : p1086 ∨ p1091)
    (h6461 : p1087 ∨ p1091)
    (h6466 : p1088 ∨ p1091)
    (h6471 : p1089 ∨ p1091)
    (h6362 : p1076 ∨ p1077 ∨ (¬ p1085) ∨ (¬ p1086) ∨ (¬ p1087) ∨ (¬ p1088) ∨ (¬ p1089)) : p1091 ∨ p1077 ∨ p1076 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1091) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1077) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1085 := by
    rcases h6451 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1086 := by
    rcases h6456 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1087 := by
    rcases h6461 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1088 := by
    rcases h6466 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1089 := by
    rcases h6471 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6362 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21481 (p1076 p1077 p1085 p1086 p1087 p1088 p1089 p1090 p1091 p1092 p1093 p1094 : Prop)
    (h6387 : p1076 ∨ p1077 ∨ (¬ p1090) ∨ (¬ p1091) ∨ (¬ p1092) ∨ (¬ p1093) ∨ (¬ p1094))
    (h6453 : p1085 ∨ p1093)
    (h6458 : p1086 ∨ p1093)
    (h6463 : p1087 ∨ p1093)
    (h6468 : p1088 ∨ p1093)
    (h6473 : p1089 ∨ p1093)
    (h6362 : p1076 ∨ p1077 ∨ (¬ p1085) ∨ (¬ p1086) ∨ (¬ p1087) ∨ (¬ p1088) ∨ (¬ p1089)) : (¬ p1091) ∨ (¬ p1092) ∨ p1076 ∨ p1077 ∨ (¬ p1094) ∨ (¬ p1090) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1091 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1092 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1077) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1094 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1090 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1093) := by
    rcases h6387 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u1)
    · exact q5
    · exact False.elim (q6 u4)
  have u7 : p1085 := by
    rcases h6453 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1086 := by
    rcases h6458 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1087 := by
    rcases h6463 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1088 := by
    rcases h6468 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1089 := by
    rcases h6473 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h6362 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21482 (p1076 p1077 p1090 p1091 p1092 p1094 : Prop)
    (h21477 : p1092 ∨ p1077 ∨ p1076)
    (h21478 : p1094 ∨ p1077 ∨ p1076)
    (h21479 : p1090 ∨ p1077 ∨ p1076)
    (h21480 : p1091 ∨ p1077 ∨ p1076)
    (h21481 : (¬ p1091) ∨ (¬ p1092) ∨ p1076 ∨ p1077 ∨ (¬ p1094) ∨ (¬ p1090)) : p1077 ∨ p1076 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1077) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr hu)
  have u2 : p1092 := by
    rcases h21477 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1094 := by
    rcases h21478 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1090 := by
    rcases h21479 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1091 := by
    rcases h21480 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21481 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step21483 (p1206 p1212 p1215 p1216 p1217 p1218 p1219 p1224 : Prop)
    (h7302 : p1215 ∨ p1224)
    (h7307 : p1216 ∨ p1224)
    (h7312 : p1217 ∨ p1224)
    (h7317 : p1218 ∨ p1224)
    (h7322 : p1219 ∨ p1224)
    (h7209 : p1206 ∨ p1212 ∨ (¬ p1215) ∨ (¬ p1216) ∨ (¬ p1217) ∨ (¬ p1218) ∨ (¬ p1219)) : p1224 ∨ p1212 ∨ p1206 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1224) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1212) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1206) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1215 := by
    rcases h7302 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1216 := by
    rcases h7307 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1217 := by
    rcases h7312 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1218 := by
    rcases h7317 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1219 := by
    rcases h7322 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7209 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21484 (p1206 p1212 p1215 p1216 p1217 p1218 p1219 p1220 : Prop)
    (h7298 : p1215 ∨ p1220)
    (h7303 : p1216 ∨ p1220)
    (h7308 : p1217 ∨ p1220)
    (h7313 : p1218 ∨ p1220)
    (h7318 : p1219 ∨ p1220)
    (h7209 : p1206 ∨ p1212 ∨ (¬ p1215) ∨ (¬ p1216) ∨ (¬ p1217) ∨ (¬ p1218) ∨ (¬ p1219)) : p1220 ∨ p1212 ∨ p1206 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1220) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1212) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1206) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1215 := by
    rcases h7298 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1216 := by
    rcases h7303 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1217 := by
    rcases h7308 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1218 := by
    rcases h7313 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1219 := by
    rcases h7318 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7209 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21485 (p1206 p1212 p1215 p1216 p1217 p1218 p1219 p1221 : Prop)
    (h7299 : p1215 ∨ p1221)
    (h7304 : p1216 ∨ p1221)
    (h7309 : p1217 ∨ p1221)
    (h7314 : p1218 ∨ p1221)
    (h7319 : p1219 ∨ p1221)
    (h7209 : p1206 ∨ p1212 ∨ (¬ p1215) ∨ (¬ p1216) ∨ (¬ p1217) ∨ (¬ p1218) ∨ (¬ p1219)) : p1221 ∨ p1212 ∨ p1206 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1221) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1212) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1206) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1215 := by
    rcases h7299 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1216 := by
    rcases h7304 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1217 := by
    rcases h7309 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1218 := by
    rcases h7314 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1219 := by
    rcases h7319 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7209 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21486 (p1206 p1212 p1215 p1216 p1217 p1218 p1219 p1222 : Prop)
    (h7300 : p1215 ∨ p1222)
    (h7305 : p1216 ∨ p1222)
    (h7310 : p1217 ∨ p1222)
    (h7315 : p1218 ∨ p1222)
    (h7320 : p1219 ∨ p1222)
    (h7209 : p1206 ∨ p1212 ∨ (¬ p1215) ∨ (¬ p1216) ∨ (¬ p1217) ∨ (¬ p1218) ∨ (¬ p1219)) : p1222 ∨ p1212 ∨ p1206 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1222) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1212) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1206) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1215 := by
    rcases h7300 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1216 := by
    rcases h7305 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1217 := by
    rcases h7310 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1218 := by
    rcases h7315 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1219 := by
    rcases h7320 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7209 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21488 (p633 p635 p643 p648 p649 p650 p651 p652 : Prop)
    (h3716 : p643 ∨ p648)
    (h3717 : p643 ∨ p649)
    (h3718 : p643 ∨ p650)
    (h3719 : p643 ∨ p651)
    (h3720 : p643 ∨ p652)
    (h3648 : p633 ∨ p635 ∨ (¬ p648) ∨ (¬ p649) ∨ (¬ p650) ∨ (¬ p651) ∨ (¬ p652)) : p643 ∨ p635 ∨ p633 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p643) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p635) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p633) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p648 := by
    rcases h3716 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p649 := by
    rcases h3717 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p650 := by
    rcases h3718 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p651 := by
    rcases h3719 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p652 := by
    rcases h3720 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3648 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21489 (p633 p635 p644 p648 p649 p650 p651 p652 : Prop)
    (h3721 : p644 ∨ p648)
    (h3722 : p644 ∨ p649)
    (h3723 : p644 ∨ p650)
    (h3724 : p644 ∨ p651)
    (h3725 : p644 ∨ p652)
    (h3648 : p633 ∨ p635 ∨ (¬ p648) ∨ (¬ p649) ∨ (¬ p650) ∨ (¬ p651) ∨ (¬ p652)) : p644 ∨ p635 ∨ p633 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p644) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p635) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p633) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p648 := by
    rcases h3721 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p649 := by
    rcases h3722 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p650 := by
    rcases h3723 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p651 := by
    rcases h3724 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p652 := by
    rcases h3725 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3648 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21490 (p633 p635 p645 p648 p649 p650 p651 p652 : Prop)
    (h3726 : p645 ∨ p648)
    (h3727 : p645 ∨ p649)
    (h3728 : p645 ∨ p650)
    (h3729 : p645 ∨ p651)
    (h3730 : p645 ∨ p652)
    (h3648 : p633 ∨ p635 ∨ (¬ p648) ∨ (¬ p649) ∨ (¬ p650) ∨ (¬ p651) ∨ (¬ p652)) : p645 ∨ p635 ∨ p633 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p645) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p635) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p633) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p648 := by
    rcases h3726 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p649 := by
    rcases h3727 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p650 := by
    rcases h3728 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p651 := by
    rcases h3729 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p652 := by
    rcases h3730 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3648 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21491 (p633 p635 p646 p648 p649 p650 p651 p652 : Prop)
    (h3731 : p646 ∨ p648)
    (h3732 : p646 ∨ p649)
    (h3733 : p646 ∨ p650)
    (h3734 : p646 ∨ p651)
    (h3735 : p646 ∨ p652)
    (h3648 : p633 ∨ p635 ∨ (¬ p648) ∨ (¬ p649) ∨ (¬ p650) ∨ (¬ p651) ∨ (¬ p652)) : p646 ∨ p635 ∨ p633 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p646) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p635) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p633) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h3648 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21493 (p124 p305 p317 p318 p319 p320 p321 p322 : Prop)
    (h1693 : p317 ∨ p318)
    (h1694 : p317 ∨ p319)
    (h1695 : p317 ∨ p320)
    (h1696 : p317 ∨ p321)
    (h1600 : p124 ∨ p305 ∨ (¬ p318) ∨ (¬ p319) ∨ (¬ p320) ∨ (¬ p321) ∨ (¬ p322)) : p317 ∨ (¬ p322) ∨ p305 ∨ p124 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p317) := fun hu => hn (Or.inl hu)
  have u1 : p322 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p305) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p318 := by
    rcases h1693 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p319 := by
    rcases h1694 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p320 := by
    rcases h1695 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p321 := by
    rcases h1696 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1600 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21494 (p124 p305 p313 p314 p315 p316 p317 p318 : Prop)
    (h1673 : p313 ∨ p318)
    (h1678 : p314 ∨ p318)
    (h1683 : p315 ∨ p318)
    (h1688 : p316 ∨ p318)
    (h1575 : p124 ∨ p305 ∨ (¬ p313) ∨ (¬ p314) ∨ (¬ p315) ∨ (¬ p316) ∨ (¬ p317)) : p318 ∨ (¬ p317) ∨ p305 ∨ p124 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p318) := fun hu => hn (Or.inl hu)
  have u1 : p317 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p305) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p313 := by
    rcases h1673 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p314 := by
    rcases h1678 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p315 := by
    rcases h1683 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p316 := by
    rcases h1688 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1575 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21495 (p124 p305 p313 p314 p315 p316 p317 p319 : Prop)
    (h1674 : p313 ∨ p319)
    (h1679 : p314 ∨ p319)
    (h1684 : p315 ∨ p319)
    (h1689 : p316 ∨ p319)
    (h1575 : p124 ∨ p305 ∨ (¬ p313) ∨ (¬ p314) ∨ (¬ p315) ∨ (¬ p316) ∨ (¬ p317)) : p319 ∨ (¬ p317) ∨ p305 ∨ p124 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p319) := fun hu => hn (Or.inl hu)
  have u1 : p317 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p305) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p313 := by
    rcases h1674 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p314 := by
    rcases h1679 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p315 := by
    rcases h1684 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p316 := by
    rcases h1689 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1575 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21496 (p124 p305 p313 p314 p315 p316 p317 p320 : Prop)
    (h1675 : p313 ∨ p320)
    (h1680 : p314 ∨ p320)
    (h1685 : p315 ∨ p320)
    (h1690 : p316 ∨ p320)
    (h1575 : p124 ∨ p305 ∨ (¬ p313) ∨ (¬ p314) ∨ (¬ p315) ∨ (¬ p316) ∨ (¬ p317)) : p320 ∨ (¬ p317) ∨ p305 ∨ p124 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p320) := fun hu => hn (Or.inl hu)
  have u1 : p317 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p305) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p313 := by
    rcases h1675 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p314 := by
    rcases h1680 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p315 := by
    rcases h1685 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p316 := by
    rcases h1690 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1575 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21497 (p124 p305 p313 p314 p315 p316 p317 p318 p319 p320 p321 p322 : Prop)
    (h21493 : p317 ∨ (¬ p322) ∨ p305 ∨ p124)
    (h21494 : p318 ∨ (¬ p317) ∨ p305 ∨ p124)
    (h21495 : p319 ∨ (¬ p317) ∨ p305 ∨ p124)
    (h21496 : p320 ∨ (¬ p317) ∨ p305 ∨ p124)
    (h1600 : p124 ∨ p305 ∨ (¬ p318) ∨ (¬ p319) ∨ (¬ p320) ∨ (¬ p321) ∨ (¬ p322))
    (h1676 : p313 ∨ p321)
    (h1681 : p314 ∨ p321)
    (h1686 : p315 ∨ p321)
    (h1691 : p316 ∨ p321)
    (h1575 : p124 ∨ p305 ∨ (¬ p313) ∨ (¬ p314) ∨ (¬ p315) ∨ (¬ p316) ∨ (¬ p317)) : (¬ p322) ∨ p305 ∨ p124 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p322 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p305) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p124) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p317 := by
    rcases h21493 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u4 : p318 := by
    rcases h21494 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u5 : p319 := by
    rcases h21495 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u6 : p320 := by
    rcases h21496 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u7 : (¬ p321) := by
    rcases h1600 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u6)
    · exact q5
    · exact False.elim (q6 u0)
  have u8 : p313 := by
    rcases h1676 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p314 := by
    rcases h1681 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p315 := by
    rcases h1686 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p316 := by
    rcases h1691 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h1575 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u3)

theorem step21498 (p124 p305 p313 p314 p315 p316 p317 p322 : Prop)
    (h21497 : (¬ p322) ∨ p305 ∨ p124)
    (h1677 : p313 ∨ p322)
    (h1682 : p314 ∨ p322)
    (h1687 : p315 ∨ p322)
    (h1692 : p316 ∨ p322)
    (h1697 : p317 ∨ p322)
    (h1575 : p124 ∨ p305 ∨ (¬ p313) ∨ (¬ p314) ∨ (¬ p315) ∨ (¬ p316) ∨ (¬ p317)) : p305 ∨ p124 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p305) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p322) := by
    rcases h21497 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p313 := by
    rcases h1677 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : p314 := by
    rcases h1682 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p315 := by
    rcases h1687 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p316 := by
    rcases h1692 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p317 := by
    rcases h1697 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h1575 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21499 (p236 p961 p967 p968 p969 p970 p971 p973 : Prop)
    (h5687 : p967 ∨ p973)
    (h5692 : p968 ∨ p973)
    (h5697 : p969 ∨ p973)
    (h5702 : p970 ∨ p973)
    (h5707 : p971 ∨ p973)
    (h5597 : p236 ∨ p961 ∨ (¬ p967) ∨ (¬ p968) ∨ (¬ p969) ∨ (¬ p970) ∨ (¬ p971)) : p973 ∨ p236 ∨ p961 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p973) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p236) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p961) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p967 := by
    rcases h5687 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p968 := by
    rcases h5692 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p969 := by
    rcases h5697 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p970 := by
    rcases h5702 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p971 := by
    rcases h5707 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5597 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21500 (p236 p961 p967 p968 p969 p970 p971 p974 : Prop)
    (h5688 : p967 ∨ p974)
    (h5693 : p968 ∨ p974)
    (h5698 : p969 ∨ p974)
    (h5703 : p970 ∨ p974)
    (h5708 : p971 ∨ p974)
    (h5597 : p236 ∨ p961 ∨ (¬ p967) ∨ (¬ p968) ∨ (¬ p969) ∨ (¬ p970) ∨ (¬ p971)) : p974 ∨ p236 ∨ p961 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p974) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p236) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p961) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p967 := by
    rcases h5688 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p968 := by
    rcases h5693 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p969 := by
    rcases h5698 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p970 := by
    rcases h5703 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p971 := by
    rcases h5708 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5597 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21501 (p236 p961 p967 p968 p969 p970 p971 p975 : Prop)
    (h5689 : p967 ∨ p975)
    (h5694 : p968 ∨ p975)
    (h5699 : p969 ∨ p975)
    (h5704 : p970 ∨ p975)
    (h5709 : p971 ∨ p975)
    (h5597 : p236 ∨ p961 ∨ (¬ p967) ∨ (¬ p968) ∨ (¬ p969) ∨ (¬ p970) ∨ (¬ p971)) : p975 ∨ p236 ∨ p961 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p975) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p236) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p961) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p967 := by
    rcases h5689 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p968 := by
    rcases h5694 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p969 := by
    rcases h5699 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p970 := by
    rcases h5704 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p971 := by
    rcases h5709 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5597 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21502 (p236 p961 p967 p968 p969 p970 p971 p976 : Prop)
    (h5690 : p967 ∨ p976)
    (h5695 : p968 ∨ p976)
    (h5700 : p969 ∨ p976)
    (h5705 : p970 ∨ p976)
    (h5710 : p971 ∨ p976)
    (h5597 : p236 ∨ p961 ∨ (¬ p967) ∨ (¬ p968) ∨ (¬ p969) ∨ (¬ p970) ∨ (¬ p971)) : p976 ∨ p236 ∨ p961 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p976) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p236) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p961) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p967 := by
    rcases h5690 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p968 := by
    rcases h5695 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p969 := by
    rcases h5700 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p970 := by
    rcases h5705 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p971 := by
    rcases h5710 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5597 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21503 (p236 p960 p961 p967 p968 p969 p970 p971 p972 p973 p974 p975 p976 : Prop)
    (h21499 : p973 ∨ p236 ∨ p961)
    (h21500 : p974 ∨ p236 ∨ p961)
    (h21501 : p975 ∨ p236 ∨ p961)
    (h21502 : p976 ∨ p236 ∨ p961)
    (h5617 : p236 ∨ p960 ∨ (¬ p972) ∨ (¬ p973) ∨ (¬ p974) ∨ (¬ p975) ∨ (¬ p976))
    (h5686 : p967 ∨ p972)
    (h5691 : p968 ∨ p972)
    (h5696 : p969 ∨ p972)
    (h5701 : p970 ∨ p972)
    (h5706 : p971 ∨ p972)
    (h5597 : p236 ∨ p961 ∨ (¬ p967) ∨ (¬ p968) ∨ (¬ p969) ∨ (¬ p970) ∨ (¬ p971)) : p236 ∨ p960 ∨ p961 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p236) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p960) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p961) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p973 := by
    rcases h21499 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u4 : p974 := by
    rcases h21500 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u5 : p975 := by
    rcases h21501 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u6 : p976 := by
    rcases h21502 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u7 : (¬ p972) := by
    rcases h5617 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u0 q0)
    · exact False.elim (u1 q1)
    · exact q2
    · exact False.elim (q3 u3)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u6)
  have u8 : p967 := by
    rcases h5686 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p968 := by
    rcases h5691 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p969 := by
    rcases h5696 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p970 := by
    rcases h5701 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u12 : p971 := by
    rcases h5706 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h5597 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u12)

theorem step21504 (p633 p635 p643 p644 p645 p646 p647 p648 p649 p650 p651 p652 : Prop)
    (h3623 : p633 ∨ p635 ∨ (¬ p643) ∨ (¬ p644) ∨ (¬ p645) ∨ (¬ p646) ∨ (¬ p647))
    (h3736 : p647 ∨ p648)
    (h3737 : p647 ∨ p649)
    (h3738 : p647 ∨ p650)
    (h3739 : p647 ∨ p651)
    (h3740 : p647 ∨ p652)
    (h3648 : p633 ∨ p635 ∨ (¬ p648) ∨ (¬ p649) ∨ (¬ p650) ∨ (¬ p651) ∨ (¬ p652)) : (¬ p646) ∨ (¬ p645) ∨ p633 ∨ p635 ∨ (¬ p643) ∨ (¬ p644) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p646 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p645 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p633) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p635) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p643 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p644 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p647) := by
    rcases h3623 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p648 := by
    rcases h3736 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p649 := by
    rcases h3737 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p650 := by
    rcases h3738 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p651 := by
    rcases h3739 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p652 := by
    rcases h3740 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h3648 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21505 (p633 p635 p643 p644 p645 p646 : Prop)
    (h21488 : p643 ∨ p635 ∨ p633)
    (h21489 : p644 ∨ p635 ∨ p633)
    (h21490 : p645 ∨ p635 ∨ p633)
    (h21491 : p646 ∨ p635 ∨ p633)
    (h21504 : (¬ p646) ∨ (¬ p645) ∨ p633 ∨ p635 ∨ (¬ p643) ∨ (¬ p644)) : p633 ∨ p635 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p635) := fun hu => hn (Or.inr hu)
  have u2 : p643 := by
    rcases h21488 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u3 : p644 := by
    rcases h21489 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u4 : p645 := by
    rcases h21490 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u5 : p646 := by
    rcases h21491 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  rcases h21504 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21506 (p1096 p1098 p1105 p1106 p1107 p1108 p1109 p1114 : Prop)
    (h6583 : p1105 ∨ p1114)
    (h6588 : p1106 ∨ p1114)
    (h6593 : p1107 ∨ p1114)
    (h6598 : p1108 ∨ p1114)
    (h6603 : p1109 ∨ p1114)
    (h6486 : p1096 ∨ p1098 ∨ (¬ p1105) ∨ (¬ p1106) ∨ (¬ p1107) ∨ (¬ p1108) ∨ (¬ p1109)) : p1114 ∨ p1098 ∨ p1096 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1114) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1098) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1105 := by
    rcases h6583 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1106 := by
    rcases h6588 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1107 := by
    rcases h6593 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1108 := by
    rcases h6598 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1109 := by
    rcases h6603 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6486 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21507 (p1096 p1098 p1105 p1106 p1107 p1108 p1109 p1110 : Prop)
    (h6579 : p1105 ∨ p1110)
    (h6584 : p1106 ∨ p1110)
    (h6589 : p1107 ∨ p1110)
    (h6594 : p1108 ∨ p1110)
    (h6599 : p1109 ∨ p1110)
    (h6486 : p1096 ∨ p1098 ∨ (¬ p1105) ∨ (¬ p1106) ∨ (¬ p1107) ∨ (¬ p1108) ∨ (¬ p1109)) : p1110 ∨ p1098 ∨ p1096 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1110) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1098) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1105 := by
    rcases h6579 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1106 := by
    rcases h6584 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1107 := by
    rcases h6589 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1108 := by
    rcases h6594 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1109 := by
    rcases h6599 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6486 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21508 (p1096 p1098 p1105 p1106 p1107 p1108 p1109 p1111 : Prop)
    (h6580 : p1105 ∨ p1111)
    (h6585 : p1106 ∨ p1111)
    (h6590 : p1107 ∨ p1111)
    (h6595 : p1108 ∨ p1111)
    (h6600 : p1109 ∨ p1111)
    (h6486 : p1096 ∨ p1098 ∨ (¬ p1105) ∨ (¬ p1106) ∨ (¬ p1107) ∨ (¬ p1108) ∨ (¬ p1109)) : p1111 ∨ p1098 ∨ p1096 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1111) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1098) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1105 := by
    rcases h6580 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1106 := by
    rcases h6585 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1107 := by
    rcases h6590 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1108 := by
    rcases h6595 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1109 := by
    rcases h6600 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6486 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21509 (p1096 p1098 p1105 p1106 p1107 p1108 p1109 p1112 : Prop)
    (h6581 : p1105 ∨ p1112)
    (h6586 : p1106 ∨ p1112)
    (h6591 : p1107 ∨ p1112)
    (h6596 : p1108 ∨ p1112)
    (h6601 : p1109 ∨ p1112)
    (h6486 : p1096 ∨ p1098 ∨ (¬ p1105) ∨ (¬ p1106) ∨ (¬ p1107) ∨ (¬ p1108) ∨ (¬ p1109)) : p1112 ∨ p1098 ∨ p1096 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1112) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1098) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1105 := by
    rcases h6581 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1106 := by
    rcases h6586 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1107 := by
    rcases h6591 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1108 := by
    rcases h6596 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1109 := by
    rcases h6601 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6486 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21510 (p1096 p1098 p1105 p1106 p1107 p1108 p1109 p1110 p1111 p1112 p1113 p1114 : Prop)
    (h6511 : p1096 ∨ p1098 ∨ (¬ p1110) ∨ (¬ p1111) ∨ (¬ p1112) ∨ (¬ p1113) ∨ (¬ p1114))
    (h6582 : p1105 ∨ p1113)
    (h6587 : p1106 ∨ p1113)
    (h6592 : p1107 ∨ p1113)
    (h6597 : p1108 ∨ p1113)
    (h6602 : p1109 ∨ p1113)
    (h6486 : p1096 ∨ p1098 ∨ (¬ p1105) ∨ (¬ p1106) ∨ (¬ p1107) ∨ (¬ p1108) ∨ (¬ p1109)) : (¬ p1112) ∨ p1098 ∨ p1096 ∨ (¬ p1114) ∨ (¬ p1110) ∨ (¬ p1111) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1112 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1098) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1114 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1111 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1113) := by
    rcases h6511 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u0)
    · exact q5
    · exact False.elim (q6 u3)
  have u7 : p1105 := by
    rcases h6582 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1106 := by
    rcases h6587 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1107 := by
    rcases h6592 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1108 := by
    rcases h6597 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1109 := by
    rcases h6602 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h6486 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21511 (p1096 p1098 p1110 p1111 p1112 p1114 : Prop)
    (h21506 : p1114 ∨ p1098 ∨ p1096)
    (h21507 : p1110 ∨ p1098 ∨ p1096)
    (h21508 : p1111 ∨ p1098 ∨ p1096)
    (h21509 : p1112 ∨ p1098 ∨ p1096)
    (h21510 : (¬ p1112) ∨ p1098 ∨ p1096 ∨ (¬ p1114) ∨ (¬ p1110) ∨ (¬ p1111)) : p1098 ∨ p1096 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1098) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr hu)
  have u2 : p1114 := by
    rcases h21506 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1110 := by
    rcases h21507 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1111 := by
    rcases h21508 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1112 := by
    rcases h21509 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21510 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step21512 (p160 p236 p304 p532 p633 p960 p961 : Prop)
    (h12577 : (¬ p160) ∨ (¬ p532) ∨ (¬ p960))
    (h18509 : (¬ p160) ∨ (¬ p236) ∨ (¬ p304) ∨ (¬ p532) ∨ (¬ p633))
    (h21503 : p236 ∨ p960 ∨ p961) : (¬ p160) ∨ (¬ p633) ∨ (¬ p532) ∨ p961 ∨ (¬ p304) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p961) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p960) := by
    rcases h12577 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact False.elim (q1 u2)
    · exact q2
  have u6 : (¬ p236) := by
    rcases h18509 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u2)
    · exact False.elim (q4 u1)
  rcases h21503 with q0 | q1 | q2
  · exact False.elim (u6 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (u3 q2)

theorem step21513 (p236 p961 p967 p968 p969 p970 p971 p972 p973 p974 p975 p976 : Prop)
    (h5622 : p236 ∨ p961 ∨ (¬ p972) ∨ (¬ p973) ∨ (¬ p974) ∨ (¬ p975) ∨ (¬ p976))
    (h5686 : p967 ∨ p972)
    (h5691 : p968 ∨ p972)
    (h5696 : p969 ∨ p972)
    (h5701 : p970 ∨ p972)
    (h5706 : p971 ∨ p972)
    (h5597 : p236 ∨ p961 ∨ (¬ p967) ∨ (¬ p968) ∨ (¬ p969) ∨ (¬ p970) ∨ (¬ p971)) : (¬ p976) ∨ (¬ p973) ∨ p961 ∨ (¬ p974) ∨ (¬ p975) ∨ p236 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p976 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p973 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p961) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p974 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p975 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p236) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p972) := by
    rcases h5622 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u5 q0)
    · exact False.elim (u2 q1)
    · exact q2
    · exact False.elim (q3 u1)
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u0)
  have u7 : p967 := by
    rcases h5686 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p968 := by
    rcases h5691 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p969 := by
    rcases h5696 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p970 := by
    rcases h5701 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p971 := by
    rcases h5706 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h5597 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u5 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21514 (p236 p961 p973 p974 p975 p976 : Prop)
    (h21499 : p973 ∨ p236 ∨ p961)
    (h21500 : p974 ∨ p236 ∨ p961)
    (h21501 : p975 ∨ p236 ∨ p961)
    (h21502 : p976 ∨ p236 ∨ p961)
    (h21513 : (¬ p976) ∨ (¬ p973) ∨ p961 ∨ (¬ p974) ∨ (¬ p975) ∨ p236) : p236 ∨ p961 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p236) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p961) := fun hu => hn (Or.inr hu)
  have u2 : p973 := by
    rcases h21499 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p974 := by
    rcases h21500 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p975 := by
    rcases h21501 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p976 := by
    rcases h21502 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21513 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (u0 q5)

theorem step21515 (p1164 p1168 p1171 p1172 p1173 p1174 p1175 p1180 : Prop)
    (h6998 : p1171 ∨ p1180)
    (h7003 : p1172 ∨ p1180)
    (h7008 : p1173 ∨ p1180)
    (h7013 : p1174 ∨ p1180)
    (h7018 : p1175 ∨ p1180)
    (h6900 : p1164 ∨ p1168 ∨ (¬ p1171) ∨ (¬ p1172) ∨ (¬ p1173) ∨ (¬ p1174) ∨ (¬ p1175)) : p1180 ∨ p1168 ∨ p1164 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1180) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1168) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1164) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1171 := by
    rcases h6998 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1172 := by
    rcases h7003 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1173 := by
    rcases h7008 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1174 := by
    rcases h7013 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1175 := by
    rcases h7018 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6900 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21516 (p1164 p1168 p1171 p1172 p1173 p1174 p1175 p1176 : Prop)
    (h6994 : p1171 ∨ p1176)
    (h6999 : p1172 ∨ p1176)
    (h7004 : p1173 ∨ p1176)
    (h7009 : p1174 ∨ p1176)
    (h7014 : p1175 ∨ p1176)
    (h6900 : p1164 ∨ p1168 ∨ (¬ p1171) ∨ (¬ p1172) ∨ (¬ p1173) ∨ (¬ p1174) ∨ (¬ p1175)) : p1176 ∨ p1168 ∨ p1164 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1176) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1168) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1164) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1171 := by
    rcases h6994 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1172 := by
    rcases h6999 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1173 := by
    rcases h7004 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1174 := by
    rcases h7009 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1175 := by
    rcases h7014 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6900 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21517 (p1164 p1168 p1171 p1172 p1173 p1174 p1175 p1177 : Prop)
    (h6995 : p1171 ∨ p1177)
    (h7000 : p1172 ∨ p1177)
    (h7005 : p1173 ∨ p1177)
    (h7010 : p1174 ∨ p1177)
    (h7015 : p1175 ∨ p1177)
    (h6900 : p1164 ∨ p1168 ∨ (¬ p1171) ∨ (¬ p1172) ∨ (¬ p1173) ∨ (¬ p1174) ∨ (¬ p1175)) : p1177 ∨ p1168 ∨ p1164 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1177) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1168) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1164) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1171 := by
    rcases h6995 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1172 := by
    rcases h7000 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1173 := by
    rcases h7005 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1174 := by
    rcases h7010 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1175 := by
    rcases h7015 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6900 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21518 (p1164 p1168 p1171 p1172 p1173 p1174 p1175 p1178 : Prop)
    (h6996 : p1171 ∨ p1178)
    (h7001 : p1172 ∨ p1178)
    (h7006 : p1173 ∨ p1178)
    (h7011 : p1174 ∨ p1178)
    (h7016 : p1175 ∨ p1178)
    (h6900 : p1164 ∨ p1168 ∨ (¬ p1171) ∨ (¬ p1172) ∨ (¬ p1173) ∨ (¬ p1174) ∨ (¬ p1175)) : p1178 ∨ p1168 ∨ p1164 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1178) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1168) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1164) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1171 := by
    rcases h6996 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1172 := by
    rcases h7001 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1173 := by
    rcases h7006 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1174 := by
    rcases h7011 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1175 := by
    rcases h7016 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6900 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21519 (p1140 p1159 p1164 p1168 p1171 p1172 p1173 p1174 p1175 p1176 p1177 p1178 p1179 p1180 : Prop)
    (h20890 : p1164 ∨ p1140)
    (h11265 : (¬ p1140) ∨ (¬ p1159))
    (h21515 : p1180 ∨ p1168 ∨ p1164)
    (h21516 : p1176 ∨ p1168 ∨ p1164)
    (h21517 : p1177 ∨ p1168 ∨ p1164)
    (h21518 : p1178 ∨ p1168 ∨ p1164)
    (h6930 : p1159 ∨ p1168 ∨ (¬ p1176) ∨ (¬ p1177) ∨ (¬ p1178) ∨ (¬ p1179) ∨ (¬ p1180))
    (h6997 : p1171 ∨ p1179)
    (h7002 : p1172 ∨ p1179)
    (h7007 : p1173 ∨ p1179)
    (h7012 : p1174 ∨ p1179)
    (h7017 : p1175 ∨ p1179)
    (h6900 : p1164 ∨ p1168 ∨ (¬ p1171) ∨ (¬ p1172) ∨ (¬ p1173) ∨ (¬ p1174) ∨ (¬ p1175)) : p1168 ∨ p1164 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1168) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1164) := fun hu => hn (Or.inr hu)
  have u2 : p1140 := by
    rcases h20890 with q0 | q1
    · exact False.elim (u1 q0)
    · exact q1
  have u3 : (¬ p1159) := by
    rcases h11265 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u4 : p1180 := by
    rcases h21515 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1176 := by
    rcases h21516 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p1177 := by
    rcases h21517 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : p1178 := by
    rcases h21518 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u8 : (¬ p1179) := by
    rcases h6930 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u6)
    · exact False.elim (q4 u7)
    · exact q5
    · exact False.elim (q6 u4)
  have u9 : p1171 := by
    rcases h6997 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u10 : p1172 := by
    rcases h7002 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u11 : p1173 := by
    rcases h7007 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u12 : p1174 := by
    rcases h7012 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u13 : p1175 := by
    rcases h7017 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h6900 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u12)
  · exact False.elim (q6 u13)

theorem step21520 (p1249 p1273 p1276 p1277 p1278 p1279 p1280 p1285 : Prop)
    (h7686 : p1276 ∨ p1285)
    (h7691 : p1277 ∨ p1285)
    (h7696 : p1278 ∨ p1285)
    (h7701 : p1279 ∨ p1285)
    (h7706 : p1280 ∨ p1285)
    (h7594 : p1249 ∨ p1273 ∨ (¬ p1276) ∨ (¬ p1277) ∨ (¬ p1278) ∨ (¬ p1279) ∨ (¬ p1280)) : p1285 ∨ p1273 ∨ p1249 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1285) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1273) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1249) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1276 := by
    rcases h7686 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1277 := by
    rcases h7691 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1278 := by
    rcases h7696 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1279 := by
    rcases h7701 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1280 := by
    rcases h7706 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7594 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21521 (p1249 p1273 p1276 p1277 p1278 p1279 p1280 p1281 : Prop)
    (h7682 : p1276 ∨ p1281)
    (h7687 : p1277 ∨ p1281)
    (h7692 : p1278 ∨ p1281)
    (h7697 : p1279 ∨ p1281)
    (h7702 : p1280 ∨ p1281)
    (h7594 : p1249 ∨ p1273 ∨ (¬ p1276) ∨ (¬ p1277) ∨ (¬ p1278) ∨ (¬ p1279) ∨ (¬ p1280)) : p1281 ∨ p1273 ∨ p1249 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1281) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1273) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1249) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1276 := by
    rcases h7682 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1277 := by
    rcases h7687 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1278 := by
    rcases h7692 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1279 := by
    rcases h7697 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1280 := by
    rcases h7702 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7594 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21522 (p1249 p1273 p1276 p1277 p1278 p1279 p1280 p1282 : Prop)
    (h7683 : p1276 ∨ p1282)
    (h7688 : p1277 ∨ p1282)
    (h7693 : p1278 ∨ p1282)
    (h7698 : p1279 ∨ p1282)
    (h7703 : p1280 ∨ p1282)
    (h7594 : p1249 ∨ p1273 ∨ (¬ p1276) ∨ (¬ p1277) ∨ (¬ p1278) ∨ (¬ p1279) ∨ (¬ p1280)) : p1282 ∨ p1273 ∨ p1249 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1282) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1273) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1249) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1276 := by
    rcases h7683 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1277 := by
    rcases h7688 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1278 := by
    rcases h7693 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1279 := by
    rcases h7698 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1280 := by
    rcases h7703 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7594 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21523 (p1249 p1273 p1276 p1277 p1278 p1279 p1280 p1283 : Prop)
    (h7684 : p1276 ∨ p1283)
    (h7689 : p1277 ∨ p1283)
    (h7694 : p1278 ∨ p1283)
    (h7699 : p1279 ∨ p1283)
    (h7704 : p1280 ∨ p1283)
    (h7594 : p1249 ∨ p1273 ∨ (¬ p1276) ∨ (¬ p1277) ∨ (¬ p1278) ∨ (¬ p1279) ∨ (¬ p1280)) : p1283 ∨ p1273 ∨ p1249 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1283) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1273) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1249) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1276 := by
    rcases h7684 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1277 := by
    rcases h7689 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1278 := by
    rcases h7694 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1279 := by
    rcases h7699 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1280 := by
    rcases h7704 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7594 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21524 (p1249 p1273 p1276 p1277 p1278 p1279 p1280 p1281 p1282 p1283 p1284 p1285 : Prop)
    (h7619 : p1249 ∨ p1273 ∨ (¬ p1281) ∨ (¬ p1282) ∨ (¬ p1283) ∨ (¬ p1284) ∨ (¬ p1285))
    (h7685 : p1276 ∨ p1284)
    (h7690 : p1277 ∨ p1284)
    (h7695 : p1278 ∨ p1284)
    (h7700 : p1279 ∨ p1284)
    (h7705 : p1280 ∨ p1284)
    (h7594 : p1249 ∨ p1273 ∨ (¬ p1276) ∨ (¬ p1277) ∨ (¬ p1278) ∨ (¬ p1279) ∨ (¬ p1280)) : (¬ p1283) ∨ (¬ p1282) ∨ p1249 ∨ p1273 ∨ (¬ p1285) ∨ (¬ p1281) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1283 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1282 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1249) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1273) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1285 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1281 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1284) := by
    rcases h7619 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u1)
    · exact False.elim (q4 u0)
    · exact q5
    · exact False.elim (q6 u4)
  have u7 : p1276 := by
    rcases h7685 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1277 := by
    rcases h7690 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1278 := by
    rcases h7695 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1279 := by
    rcases h7700 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1280 := by
    rcases h7705 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h7594 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21525 (p1249 p1273 p1281 p1282 p1283 p1285 : Prop)
    (h21520 : p1285 ∨ p1273 ∨ p1249)
    (h21521 : p1281 ∨ p1273 ∨ p1249)
    (h21522 : p1282 ∨ p1273 ∨ p1249)
    (h21523 : p1283 ∨ p1273 ∨ p1249)
    (h21524 : (¬ p1283) ∨ (¬ p1282) ∨ p1249 ∨ p1273 ∨ (¬ p1285) ∨ (¬ p1281)) : p1273 ∨ p1249 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1273) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1249) := fun hu => hn (Or.inr hu)
  have u2 : p1285 := by
    rcases h21520 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1281 := by
    rcases h21521 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1282 := by
    rcases h21522 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1283 := by
    rcases h21523 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21524 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21526 (p234 p1187 p1196 p1201 p1202 p1203 p1204 p1205 : Prop)
    (h7163 : p1196 ∨ p1201)
    (h7164 : p1196 ∨ p1202)
    (h7165 : p1196 ∨ p1203)
    (h7166 : p1196 ∨ p1204)
    (h7167 : p1196 ∨ p1205)
    (h7100 : p234 ∨ p1187 ∨ (¬ p1201) ∨ (¬ p1202) ∨ (¬ p1203) ∨ (¬ p1204) ∨ (¬ p1205)) : p1196 ∨ p1187 ∨ p234 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1196) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1187) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p234) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1201 := by
    rcases h7163 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1202 := by
    rcases h7164 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1203 := by
    rcases h7165 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1204 := by
    rcases h7166 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1205 := by
    rcases h7167 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7100 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21527 (p234 p1187 p1197 p1201 p1202 p1203 p1204 p1205 : Prop)
    (h7168 : p1197 ∨ p1201)
    (h7169 : p1197 ∨ p1202)
    (h7170 : p1197 ∨ p1203)
    (h7171 : p1197 ∨ p1204)
    (h7172 : p1197 ∨ p1205)
    (h7100 : p234 ∨ p1187 ∨ (¬ p1201) ∨ (¬ p1202) ∨ (¬ p1203) ∨ (¬ p1204) ∨ (¬ p1205)) : p1197 ∨ p1187 ∨ p234 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1197) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1187) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h7100 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21528 (p234 p1187 p1198 p1201 p1202 p1203 p1204 p1205 : Prop)
    (h7173 : p1198 ∨ p1201)
    (h7174 : p1198 ∨ p1202)
    (h7175 : p1198 ∨ p1203)
    (h7176 : p1198 ∨ p1204)
    (h7177 : p1198 ∨ p1205)
    (h7100 : p234 ∨ p1187 ∨ (¬ p1201) ∨ (¬ p1202) ∨ (¬ p1203) ∨ (¬ p1204) ∨ (¬ p1205)) : p1198 ∨ p1187 ∨ p234 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1198) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1187) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p234) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1201 := by
    rcases h7173 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1202 := by
    rcases h7174 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1203 := by
    rcases h7175 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1204 := by
    rcases h7176 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1205 := by
    rcases h7177 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7100 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21529 (p234 p1187 p1199 p1201 p1202 p1203 p1204 p1205 : Prop)
    (h7178 : p1199 ∨ p1201)
    (h7179 : p1199 ∨ p1202)
    (h7180 : p1199 ∨ p1203)
    (h7181 : p1199 ∨ p1204)
    (h7182 : p1199 ∨ p1205)
    (h7100 : p234 ∨ p1187 ∨ (¬ p1201) ∨ (¬ p1202) ∨ (¬ p1203) ∨ (¬ p1204) ∨ (¬ p1205)) : p1199 ∨ p1187 ∨ p234 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1199) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1187) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p234) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1201 := by
    rcases h7178 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1202 := by
    rcases h7179 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1203 := by
    rcases h7180 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1204 := by
    rcases h7181 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1205 := by
    rcases h7182 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7100 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21530 (p234 p1187 p1196 p1197 p1198 p1199 p1200 p1201 p1202 p1203 p1204 p1205 : Prop)
    (h7075 : p234 ∨ p1187 ∨ (¬ p1196) ∨ (¬ p1197) ∨ (¬ p1198) ∨ (¬ p1199) ∨ (¬ p1200))
    (h7183 : p1200 ∨ p1201)
    (h7184 : p1200 ∨ p1202)
    (h7185 : p1200 ∨ p1203)
    (h7186 : p1200 ∨ p1204)
    (h7187 : p1200 ∨ p1205)
    (h7100 : p234 ∨ p1187 ∨ (¬ p1201) ∨ (¬ p1202) ∨ (¬ p1203) ∨ (¬ p1204) ∨ (¬ p1205)) : (¬ p1199) ∨ (¬ p1198) ∨ p234 ∨ p1187 ∨ (¬ p1196) ∨ (¬ p1197) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1199 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1198 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p234) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1187) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1196 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1197 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1200) := by
    rcases h7075 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p1201 := by
    rcases h7183 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1202 := by
    rcases h7184 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1203 := by
    rcases h7185 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1204 := by
    rcases h7186 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1205 := by
    rcases h7187 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h7100 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21531 (p234 p1187 p1196 p1197 p1198 p1199 : Prop)
    (h21526 : p1196 ∨ p1187 ∨ p234)
    (h21527 : p1197 ∨ p1187 ∨ p234)
    (h21528 : p1198 ∨ p1187 ∨ p234)
    (h21529 : p1199 ∨ p1187 ∨ p234)
    (h21530 : (¬ p1199) ∨ (¬ p1198) ∨ p234 ∨ p1187 ∨ (¬ p1196) ∨ (¬ p1197)) : p1187 ∨ p234 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1187) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p234) := fun hu => hn (Or.inr hu)
  have u2 : p1196 := by
    rcases h21526 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1197 := by
    rcases h21527 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1198 := by
    rcases h21528 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1199 := by
    rcases h21529 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21530 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21532 (p1117 p1121 p1125 p1130 p1131 p1132 p1133 p1134 : Prop)
    (h6708 : p1125 ∨ p1130)
    (h6709 : p1125 ∨ p1131)
    (h6710 : p1125 ∨ p1132)
    (h6711 : p1125 ∨ p1133)
    (h6712 : p1125 ∨ p1134)
    (h6633 : p1117 ∨ p1121 ∨ (¬ p1130) ∨ (¬ p1131) ∨ (¬ p1132) ∨ (¬ p1133) ∨ (¬ p1134)) : p1125 ∨ p1121 ∨ p1117 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1125) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1121) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1117) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1130 := by
    rcases h6708 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1131 := by
    rcases h6709 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1132 := by
    rcases h6710 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1133 := by
    rcases h6711 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1134 := by
    rcases h6712 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6633 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21533 (p1117 p1121 p1126 p1130 p1131 p1132 p1133 p1134 : Prop)
    (h6713 : p1126 ∨ p1130)
    (h6714 : p1126 ∨ p1131)
    (h6715 : p1126 ∨ p1132)
    (h6716 : p1126 ∨ p1133)
    (h6717 : p1126 ∨ p1134)
    (h6633 : p1117 ∨ p1121 ∨ (¬ p1130) ∨ (¬ p1131) ∨ (¬ p1132) ∨ (¬ p1133) ∨ (¬ p1134)) : p1126 ∨ p1121 ∨ p1117 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1126) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1121) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1117) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1130 := by
    rcases h6713 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1131 := by
    rcases h6714 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1132 := by
    rcases h6715 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1133 := by
    rcases h6716 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1134 := by
    rcases h6717 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6633 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21534 (p1117 p1121 p1127 p1130 p1131 p1132 p1133 p1134 : Prop)
    (h6718 : p1127 ∨ p1130)
    (h6719 : p1127 ∨ p1131)
    (h6720 : p1127 ∨ p1132)
    (h6721 : p1127 ∨ p1133)
    (h6722 : p1127 ∨ p1134)
    (h6633 : p1117 ∨ p1121 ∨ (¬ p1130) ∨ (¬ p1131) ∨ (¬ p1132) ∨ (¬ p1133) ∨ (¬ p1134)) : p1127 ∨ p1121 ∨ p1117 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1127) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1121) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1117) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1130 := by
    rcases h6718 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1131 := by
    rcases h6719 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1132 := by
    rcases h6720 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1133 := by
    rcases h6721 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1134 := by
    rcases h6722 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6633 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21535 (p1117 p1121 p1128 p1130 p1131 p1132 p1133 p1134 : Prop)
    (h6723 : p1128 ∨ p1130)
    (h6724 : p1128 ∨ p1131)
    (h6725 : p1128 ∨ p1132)
    (h6726 : p1128 ∨ p1133)
    (h6727 : p1128 ∨ p1134)
    (h6633 : p1117 ∨ p1121 ∨ (¬ p1130) ∨ (¬ p1131) ∨ (¬ p1132) ∨ (¬ p1133) ∨ (¬ p1134)) : p1128 ∨ p1121 ∨ p1117 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1128) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1121) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1117) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h6633 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21536 (p1117 p1121 p1125 p1126 p1127 p1128 p1129 p1130 p1131 p1132 p1133 p1134 : Prop)
    (h6608 : p1117 ∨ p1121 ∨ (¬ p1125) ∨ (¬ p1126) ∨ (¬ p1127) ∨ (¬ p1128) ∨ (¬ p1129))
    (h6728 : p1129 ∨ p1130)
    (h6729 : p1129 ∨ p1131)
    (h6730 : p1129 ∨ p1132)
    (h6731 : p1129 ∨ p1133)
    (h6732 : p1129 ∨ p1134)
    (h6633 : p1117 ∨ p1121 ∨ (¬ p1130) ∨ (¬ p1131) ∨ (¬ p1132) ∨ (¬ p1133) ∨ (¬ p1134)) : (¬ p1128) ∨ (¬ p1127) ∨ p1117 ∨ p1121 ∨ (¬ p1125) ∨ (¬ p1126) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1128 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1117) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1121) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1129) := by
    rcases h6608 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p1130 := by
    rcases h6728 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1131 := by
    rcases h6729 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1132 := by
    rcases h6730 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1133 := by
    rcases h6731 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1134 := by
    rcases h6732 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h6633 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21537 (p1117 p1121 p1125 p1126 p1127 p1128 : Prop)
    (h21532 : p1125 ∨ p1121 ∨ p1117)
    (h21533 : p1126 ∨ p1121 ∨ p1117)
    (h21534 : p1127 ∨ p1121 ∨ p1117)
    (h21535 : p1128 ∨ p1121 ∨ p1117)
    (h21536 : (¬ p1128) ∨ (¬ p1127) ∨ p1117 ∨ p1121 ∨ (¬ p1125) ∨ (¬ p1126)) : p1121 ∨ p1117 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1121) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1117) := fun hu => hn (Or.inr hu)
  have u2 : p1125 := by
    rcases h21532 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1126 := by
    rcases h21533 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1127 := by
    rcases h21534 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1128 := by
    rcases h21535 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21536 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21538 (p1055 p1060 p1064 p1065 p1066 p1067 p1068 p1073 : Prop)
    (h6327 : p1064 ∨ p1073)
    (h6332 : p1065 ∨ p1073)
    (h6337 : p1066 ∨ p1073)
    (h6342 : p1067 ∨ p1073)
    (h6347 : p1068 ∨ p1073)
    (h6233 : p1055 ∨ p1060 ∨ (¬ p1064) ∨ (¬ p1065) ∨ (¬ p1066) ∨ (¬ p1067) ∨ (¬ p1068)) : p1073 ∨ p1060 ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1073) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1060) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1064 := by
    rcases h6327 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1065 := by
    rcases h6332 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1066 := by
    rcases h6337 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1067 := by
    rcases h6342 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1068 := by
    rcases h6347 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6233 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21539 (p1055 p1060 p1064 p1065 p1066 p1067 p1068 p1069 : Prop)
    (h6323 : p1064 ∨ p1069)
    (h6328 : p1065 ∨ p1069)
    (h6333 : p1066 ∨ p1069)
    (h6338 : p1067 ∨ p1069)
    (h6343 : p1068 ∨ p1069)
    (h6233 : p1055 ∨ p1060 ∨ (¬ p1064) ∨ (¬ p1065) ∨ (¬ p1066) ∨ (¬ p1067) ∨ (¬ p1068)) : p1069 ∨ p1060 ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1069) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1060) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1064 := by
    rcases h6323 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1065 := by
    rcases h6328 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1066 := by
    rcases h6333 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1067 := by
    rcases h6338 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1068 := by
    rcases h6343 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6233 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21540 (p1055 p1060 p1064 p1065 p1066 p1067 p1068 p1070 : Prop)
    (h6324 : p1064 ∨ p1070)
    (h6329 : p1065 ∨ p1070)
    (h6334 : p1066 ∨ p1070)
    (h6339 : p1067 ∨ p1070)
    (h6344 : p1068 ∨ p1070)
    (h6233 : p1055 ∨ p1060 ∨ (¬ p1064) ∨ (¬ p1065) ∨ (¬ p1066) ∨ (¬ p1067) ∨ (¬ p1068)) : p1070 ∨ p1060 ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1070) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1060) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1064 := by
    rcases h6324 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1065 := by
    rcases h6329 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1066 := by
    rcases h6334 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1067 := by
    rcases h6339 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1068 := by
    rcases h6344 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6233 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21541 (p1055 p1060 p1064 p1065 p1066 p1067 p1068 p1071 : Prop)
    (h6325 : p1064 ∨ p1071)
    (h6330 : p1065 ∨ p1071)
    (h6335 : p1066 ∨ p1071)
    (h6340 : p1067 ∨ p1071)
    (h6345 : p1068 ∨ p1071)
    (h6233 : p1055 ∨ p1060 ∨ (¬ p1064) ∨ (¬ p1065) ∨ (¬ p1066) ∨ (¬ p1067) ∨ (¬ p1068)) : p1071 ∨ p1060 ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1071) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1060) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1064 := by
    rcases h6325 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1065 := by
    rcases h6330 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1066 := by
    rcases h6335 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1067 := by
    rcases h6340 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1068 := by
    rcases h6345 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6233 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21543 (p1489 p1508 p1517 p1518 p1519 p1520 p1521 p1522 : Prop)
    (h9278 : p1517 ∨ p1522)
    (h9283 : p1518 ∨ p1522)
    (h9288 : p1519 ∨ p1522)
    (h9293 : p1520 ∨ p1522)
    (h9298 : p1521 ∨ p1522)
    (h9190 : p1489 ∨ p1508 ∨ (¬ p1517) ∨ (¬ p1518) ∨ (¬ p1519) ∨ (¬ p1520) ∨ (¬ p1521)) : p1522 ∨ p1508 ∨ p1489 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1522) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1508) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1489) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1517 := by
    rcases h9278 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1518 := by
    rcases h9283 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1519 := by
    rcases h9288 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1520 := by
    rcases h9293 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1521 := by
    rcases h9298 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h9190 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21544 (p1489 p1508 p1517 p1518 p1519 p1520 p1521 p1523 : Prop)
    (h9279 : p1517 ∨ p1523)
    (h9284 : p1518 ∨ p1523)
    (h9289 : p1519 ∨ p1523)
    (h9294 : p1520 ∨ p1523)
    (h9299 : p1521 ∨ p1523)
    (h9190 : p1489 ∨ p1508 ∨ (¬ p1517) ∨ (¬ p1518) ∨ (¬ p1519) ∨ (¬ p1520) ∨ (¬ p1521)) : p1523 ∨ p1508 ∨ p1489 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1523) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1508) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1489) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1517 := by
    rcases h9279 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1518 := by
    rcases h9284 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1519 := by
    rcases h9289 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1520 := by
    rcases h9294 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1521 := by
    rcases h9299 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h9190 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21545 (p1489 p1508 p1517 p1518 p1519 p1520 p1521 p1524 : Prop)
    (h9280 : p1517 ∨ p1524)
    (h9285 : p1518 ∨ p1524)
    (h9290 : p1519 ∨ p1524)
    (h9295 : p1520 ∨ p1524)
    (h9300 : p1521 ∨ p1524)
    (h9190 : p1489 ∨ p1508 ∨ (¬ p1517) ∨ (¬ p1518) ∨ (¬ p1519) ∨ (¬ p1520) ∨ (¬ p1521)) : p1524 ∨ p1508 ∨ p1489 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1524) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1508) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1489) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1517 := by
    rcases h9280 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1518 := by
    rcases h9285 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1519 := by
    rcases h9290 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1520 := by
    rcases h9295 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1521 := by
    rcases h9300 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h9190 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21546 (p1489 p1508 p1517 p1518 p1519 p1520 p1521 p1525 : Prop)
    (h9281 : p1517 ∨ p1525)
    (h9286 : p1518 ∨ p1525)
    (h9291 : p1519 ∨ p1525)
    (h9296 : p1520 ∨ p1525)
    (h9301 : p1521 ∨ p1525)
    (h9190 : p1489 ∨ p1508 ∨ (¬ p1517) ∨ (¬ p1518) ∨ (¬ p1519) ∨ (¬ p1520) ∨ (¬ p1521)) : p1525 ∨ p1508 ∨ p1489 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1525) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1508) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1489) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1517 := by
    rcases h9281 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1518 := by
    rcases h9286 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1519 := by
    rcases h9291 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1520 := by
    rcases h9296 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1521 := by
    rcases h9301 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h9190 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21547 (p1489 p1508 p1517 p1518 p1519 p1520 p1521 p1522 p1523 p1524 p1525 p1526 : Prop)
    (h9215 : p1489 ∨ p1508 ∨ (¬ p1522) ∨ (¬ p1523) ∨ (¬ p1524) ∨ (¬ p1525) ∨ (¬ p1526))
    (h9282 : p1517 ∨ p1526)
    (h9287 : p1518 ∨ p1526)
    (h9292 : p1519 ∨ p1526)
    (h9297 : p1520 ∨ p1526)
    (h9302 : p1521 ∨ p1526)
    (h9190 : p1489 ∨ p1508 ∨ (¬ p1517) ∨ (¬ p1518) ∨ (¬ p1519) ∨ (¬ p1520) ∨ (¬ p1521)) : (¬ p1525) ∨ (¬ p1524) ∨ p1489 ∨ p1508 ∨ (¬ p1522) ∨ (¬ p1523) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1525 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1524 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1489) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1508) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1522 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1523 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1526) := by
    rcases h9215 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p1517 := by
    rcases h9282 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1518 := by
    rcases h9287 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1519 := by
    rcases h9292 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1520 := by
    rcases h9297 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1521 := by
    rcases h9302 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h9190 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21548 (p1489 p1508 p1522 p1523 p1524 p1525 : Prop)
    (h21543 : p1522 ∨ p1508 ∨ p1489)
    (h21544 : p1523 ∨ p1508 ∨ p1489)
    (h21545 : p1524 ∨ p1508 ∨ p1489)
    (h21546 : p1525 ∨ p1508 ∨ p1489)
    (h21547 : (¬ p1525) ∨ (¬ p1524) ∨ p1489 ∨ p1508 ∨ (¬ p1522) ∨ (¬ p1523)) : p1508 ∨ p1489 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1508) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1489) := fun hu => hn (Or.inr hu)
  have u2 : p1522 := by
    rcases h21543 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1523 := by
    rcases h21544 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1524 := by
    rcases h21545 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1525 := by
    rcases h21546 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21547 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21549 (p11 p1496 p1502 p1503 p1504 p1505 p1506 p1507 : Prop)
    (h9173 : p1502 ∨ p1503)
    (h9174 : p1502 ∨ p1504)
    (h9175 : p1502 ∨ p1505)
    (h9176 : p1502 ∨ p1506)
    (h9177 : p1502 ∨ p1507)
    (h9089 : p11 ∨ p1496 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507)) : p1502 ∨ p1496 ∨ p11 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1502) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1496) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p11) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1503 := by
    rcases h9173 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1504 := by
    rcases h9174 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1505 := by
    rcases h9175 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1506 := by
    rcases h9176 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1507 := by
    rcases h9177 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h9089 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21550 (p11 p1496 p1498 p1503 p1504 p1505 p1506 p1507 : Prop)
    (h9153 : p1498 ∨ p1503)
    (h9154 : p1498 ∨ p1504)
    (h9155 : p1498 ∨ p1505)
    (h9156 : p1498 ∨ p1506)
    (h9157 : p1498 ∨ p1507)
    (h9089 : p11 ∨ p1496 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507)) : p1498 ∨ p1496 ∨ p11 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1498) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1496) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p11) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1503 := by
    rcases h9153 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1504 := by
    rcases h9154 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1505 := by
    rcases h9155 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1506 := by
    rcases h9156 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1507 := by
    rcases h9157 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h9089 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21551 (p11 p1496 p1499 p1503 p1504 p1505 p1506 p1507 : Prop)
    (h9158 : p1499 ∨ p1503)
    (h9159 : p1499 ∨ p1504)
    (h9160 : p1499 ∨ p1505)
    (h9161 : p1499 ∨ p1506)
    (h9162 : p1499 ∨ p1507)
    (h9089 : p11 ∨ p1496 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507)) : p1499 ∨ p1496 ∨ p11 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1499) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1496) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p11) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1503 := by
    rcases h9158 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1504 := by
    rcases h9159 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1505 := by
    rcases h9160 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1506 := by
    rcases h9161 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1507 := by
    rcases h9162 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h9089 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21552 (p11 p1496 p1500 p1503 p1504 p1505 p1506 p1507 : Prop)
    (h9163 : p1500 ∨ p1503)
    (h9164 : p1500 ∨ p1504)
    (h9165 : p1500 ∨ p1505)
    (h9166 : p1500 ∨ p1506)
    (h9167 : p1500 ∨ p1507)
    (h9089 : p11 ∨ p1496 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507)) : p1500 ∨ p1496 ∨ p11 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1500) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1496) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p11) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1503 := by
    rcases h9163 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1504 := by
    rcases h9164 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1505 := by
    rcases h9165 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1506 := by
    rcases h9166 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1507 := by
    rcases h9167 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h9089 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21553 (p11 p1496 p1498 p1499 p1500 p1501 p1502 p1503 p1504 p1505 p1506 p1507 : Prop)
    (h9064 : p11 ∨ p1496 ∨ (¬ p1498) ∨ (¬ p1499) ∨ (¬ p1500) ∨ (¬ p1501) ∨ (¬ p1502))
    (h9168 : p1501 ∨ p1503)
    (h9169 : p1501 ∨ p1504)
    (h9170 : p1501 ∨ p1505)
    (h9171 : p1501 ∨ p1506)
    (h9172 : p1501 ∨ p1507)
    (h9089 : p11 ∨ p1496 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507)) : (¬ p1500) ∨ p1496 ∨ p11 ∨ (¬ p1499) ∨ (¬ p1502) ∨ (¬ p1498) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1496) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1502 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1501) := by
    rcases h9064 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u3)
    · exact False.elim (q4 u0)
    · exact q5
    · exact False.elim (q6 u4)
  have u7 : p1503 := by
    rcases h9168 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1504 := by
    rcases h9169 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1505 := by
    rcases h9170 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1506 := by
    rcases h9171 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1507 := by
    rcases h9172 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h9089 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21554 (p11 p1496 p1498 p1499 p1500 p1502 : Prop)
    (h21549 : p1502 ∨ p1496 ∨ p11)
    (h21550 : p1498 ∨ p1496 ∨ p11)
    (h21551 : p1499 ∨ p1496 ∨ p11)
    (h21552 : p1500 ∨ p1496 ∨ p11)
    (h21553 : (¬ p1500) ∨ p1496 ∨ p11 ∨ (¬ p1499) ∨ (¬ p1502) ∨ (¬ p1498)) : p1496 ∨ p11 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1496) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p11) := fun hu => hn (Or.inr hu)
  have u2 : p1502 := by
    rcases h21549 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1498 := by
    rcases h21550 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1499 := by
    rcases h21551 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1500 := by
    rcases h21552 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21553 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21555 (p1141 p1145 p1149 p1150 p1151 p1152 p1153 p1158 : Prop)
    (h6868 : p1149 ∨ p1158)
    (h6873 : p1150 ∨ p1158)
    (h6878 : p1151 ∨ p1158)
    (h6883 : p1152 ∨ p1158)
    (h6888 : p1153 ∨ p1158)
    (h6774 : p1141 ∨ p1145 ∨ (¬ p1149) ∨ (¬ p1150) ∨ (¬ p1151) ∨ (¬ p1152) ∨ (¬ p1153)) : p1158 ∨ p1145 ∨ p1141 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1158) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1145) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1141) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1149 := by
    rcases h6868 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1150 := by
    rcases h6873 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1151 := by
    rcases h6878 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1152 := by
    rcases h6883 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1153 := by
    rcases h6888 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6774 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21556 (p1141 p1145 p1149 p1150 p1151 p1152 p1153 p1154 : Prop)
    (h6864 : p1149 ∨ p1154)
    (h6869 : p1150 ∨ p1154)
    (h6874 : p1151 ∨ p1154)
    (h6879 : p1152 ∨ p1154)
    (h6884 : p1153 ∨ p1154)
    (h6774 : p1141 ∨ p1145 ∨ (¬ p1149) ∨ (¬ p1150) ∨ (¬ p1151) ∨ (¬ p1152) ∨ (¬ p1153)) : p1154 ∨ p1145 ∨ p1141 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1154) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1145) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1141) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1149 := by
    rcases h6864 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1150 := by
    rcases h6869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1151 := by
    rcases h6874 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1152 := by
    rcases h6879 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1153 := by
    rcases h6884 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6774 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21557 (p1141 p1145 p1149 p1150 p1151 p1152 p1153 p1155 : Prop)
    (h6865 : p1149 ∨ p1155)
    (h6870 : p1150 ∨ p1155)
    (h6875 : p1151 ∨ p1155)
    (h6880 : p1152 ∨ p1155)
    (h6885 : p1153 ∨ p1155)
    (h6774 : p1141 ∨ p1145 ∨ (¬ p1149) ∨ (¬ p1150) ∨ (¬ p1151) ∨ (¬ p1152) ∨ (¬ p1153)) : p1155 ∨ p1145 ∨ p1141 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1155) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1145) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1141) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1149 := by
    rcases h6865 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1150 := by
    rcases h6870 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1151 := by
    rcases h6875 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1152 := by
    rcases h6880 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1153 := by
    rcases h6885 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6774 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21558 (p1141 p1145 p1149 p1150 p1151 p1152 p1153 p1156 : Prop)
    (h6866 : p1149 ∨ p1156)
    (h6871 : p1150 ∨ p1156)
    (h6876 : p1151 ∨ p1156)
    (h6881 : p1152 ∨ p1156)
    (h6886 : p1153 ∨ p1156)
    (h6774 : p1141 ∨ p1145 ∨ (¬ p1149) ∨ (¬ p1150) ∨ (¬ p1151) ∨ (¬ p1152) ∨ (¬ p1153)) : p1156 ∨ p1145 ∨ p1141 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1156) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1145) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1141) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1149 := by
    rcases h6866 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1150 := by
    rcases h6871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1151 := by
    rcases h6876 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1152 := by
    rcases h6881 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1153 := by
    rcases h6886 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6774 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21559 (p1141 p1145 p1149 p1150 p1151 p1152 p1153 p1154 p1155 p1156 p1157 p1158 : Prop)
    (h6799 : p1141 ∨ p1145 ∨ (¬ p1154) ∨ (¬ p1155) ∨ (¬ p1156) ∨ (¬ p1157) ∨ (¬ p1158))
    (h6867 : p1149 ∨ p1157)
    (h6872 : p1150 ∨ p1157)
    (h6877 : p1151 ∨ p1157)
    (h6882 : p1152 ∨ p1157)
    (h6887 : p1153 ∨ p1157)
    (h6774 : p1141 ∨ p1145 ∨ (¬ p1149) ∨ (¬ p1150) ∨ (¬ p1151) ∨ (¬ p1152) ∨ (¬ p1153)) : (¬ p1156) ∨ p1145 ∨ p1141 ∨ (¬ p1158) ∨ (¬ p1154) ∨ (¬ p1155) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1145) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1141) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1154 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1155 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1157) := by
    rcases h6799 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u0)
    · exact q5
    · exact False.elim (q6 u3)
  have u7 : p1149 := by
    rcases h6867 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1150 := by
    rcases h6872 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1151 := by
    rcases h6877 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1152 := by
    rcases h6882 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1153 := by
    rcases h6887 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h6774 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21560 (p1141 p1145 p1154 p1155 p1156 p1158 : Prop)
    (h21555 : p1158 ∨ p1145 ∨ p1141)
    (h21556 : p1154 ∨ p1145 ∨ p1141)
    (h21557 : p1155 ∨ p1145 ∨ p1141)
    (h21558 : p1156 ∨ p1145 ∨ p1141)
    (h21559 : (¬ p1156) ∨ p1145 ∨ p1141 ∨ (¬ p1158) ∨ (¬ p1154) ∨ (¬ p1155)) : p1145 ∨ p1141 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1145) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1141) := fun hu => hn (Or.inr hu)
  have u2 : p1158 := by
    rcases h21555 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1154 := by
    rcases h21556 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1155 := by
    rcases h21557 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1156 := by
    rcases h21558 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21559 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step21561 (p1035 p1465 p1474 p1475 p1476 p1477 p1478 p1479 : Prop)
    (h9009 : p1474 ∨ p1479)
    (h9014 : p1475 ∨ p1479)
    (h9019 : p1476 ∨ p1479)
    (h9024 : p1477 ∨ p1479)
    (h9029 : p1478 ∨ p1479)
    (h8921 : p1035 ∨ p1465 ∨ (¬ p1474) ∨ (¬ p1475) ∨ (¬ p1476) ∨ (¬ p1477) ∨ (¬ p1478)) : p1479 ∨ p1465 ∨ p1035 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1479) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1465) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1035) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1474 := by
    rcases h9009 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1475 := by
    rcases h9014 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1476 := by
    rcases h9019 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1477 := by
    rcases h9024 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1478 := by
    rcases h9029 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8921 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21562 (p1035 p1465 p1474 p1475 p1476 p1477 p1478 p1480 : Prop)
    (h9010 : p1474 ∨ p1480)
    (h9015 : p1475 ∨ p1480)
    (h9020 : p1476 ∨ p1480)
    (h9025 : p1477 ∨ p1480)
    (h9030 : p1478 ∨ p1480)
    (h8921 : p1035 ∨ p1465 ∨ (¬ p1474) ∨ (¬ p1475) ∨ (¬ p1476) ∨ (¬ p1477) ∨ (¬ p1478)) : p1480 ∨ p1465 ∨ p1035 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1480) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1465) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1035) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1474 := by
    rcases h9010 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1475 := by
    rcases h9015 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1476 := by
    rcases h9020 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1477 := by
    rcases h9025 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1478 := by
    rcases h9030 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8921 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21563 (p1035 p1465 p1474 p1475 p1476 p1477 p1478 p1481 : Prop)
    (h9011 : p1474 ∨ p1481)
    (h9016 : p1475 ∨ p1481)
    (h9021 : p1476 ∨ p1481)
    (h9026 : p1477 ∨ p1481)
    (h9031 : p1478 ∨ p1481)
    (h8921 : p1035 ∨ p1465 ∨ (¬ p1474) ∨ (¬ p1475) ∨ (¬ p1476) ∨ (¬ p1477) ∨ (¬ p1478)) : p1481 ∨ p1465 ∨ p1035 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1481) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1465) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1035) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1474 := by
    rcases h9011 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1475 := by
    rcases h9016 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1476 := by
    rcases h9021 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1477 := by
    rcases h9026 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1478 := by
    rcases h9031 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8921 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21564 (p1035 p1465 p1474 p1475 p1476 p1477 p1478 p1482 : Prop)
    (h9012 : p1474 ∨ p1482)
    (h9017 : p1475 ∨ p1482)
    (h9022 : p1476 ∨ p1482)
    (h9027 : p1477 ∨ p1482)
    (h9032 : p1478 ∨ p1482)
    (h8921 : p1035 ∨ p1465 ∨ (¬ p1474) ∨ (¬ p1475) ∨ (¬ p1476) ∨ (¬ p1477) ∨ (¬ p1478)) : p1482 ∨ p1465 ∨ p1035 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1482) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1465) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h8921 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21565 (p1035 p1465 p1474 p1475 p1476 p1477 p1478 p1479 p1480 p1481 p1482 p1483 : Prop)
    (h8946 : p1035 ∨ p1465 ∨ (¬ p1479) ∨ (¬ p1480) ∨ (¬ p1481) ∨ (¬ p1482) ∨ (¬ p1483))
    (h9013 : p1474 ∨ p1483)
    (h9018 : p1475 ∨ p1483)
    (h9023 : p1476 ∨ p1483)
    (h9028 : p1477 ∨ p1483)
    (h9033 : p1478 ∨ p1483)
    (h8921 : p1035 ∨ p1465 ∨ (¬ p1474) ∨ (¬ p1475) ∨ (¬ p1476) ∨ (¬ p1477) ∨ (¬ p1478)) : (¬ p1482) ∨ (¬ p1481) ∨ p1035 ∨ p1465 ∨ (¬ p1479) ∨ (¬ p1480) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1482 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1035) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1465) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1479 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1480 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1483) := by
    rcases h8946 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p1474 := by
    rcases h9013 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1475 := by
    rcases h9018 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1476 := by
    rcases h9023 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1477 := by
    rcases h9028 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1478 := by
    rcases h9033 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h8921 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21566 (p1035 p1465 p1479 p1480 p1481 p1482 : Prop)
    (h21561 : p1479 ∨ p1465 ∨ p1035)
    (h21562 : p1480 ∨ p1465 ∨ p1035)
    (h21563 : p1481 ∨ p1465 ∨ p1035)
    (h21564 : p1482 ∨ p1465 ∨ p1035)
    (h21565 : (¬ p1482) ∨ (¬ p1481) ∨ p1035 ∨ p1465 ∨ (¬ p1479) ∨ (¬ p1480)) : p1465 ∨ p1035 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1465) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1035) := fun hu => hn (Or.inr hu)
  have u2 : p1479 := by
    rcases h21561 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1480 := by
    rcases h21562 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1481 := by
    rcases h21563 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1482 := by
    rcases h21564 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21565 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21567 (p161 p1225 p1432 p1433 p1434 p1435 p1436 p1437 : Prop)
    (h8701 : p1432 ∨ p1437)
    (h8706 : p1433 ∨ p1437)
    (h8711 : p1434 ∨ p1437)
    (h8716 : p1435 ∨ p1437)
    (h8721 : p1436 ∨ p1437)
    (h8613 : p161 ∨ p1225 ∨ (¬ p1432) ∨ (¬ p1433) ∨ (¬ p1434) ∨ (¬ p1435) ∨ (¬ p1436)) : p1437 ∨ p161 ∨ p1225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1437) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p161) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1225) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1432 := by
    rcases h8701 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1433 := by
    rcases h8706 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1434 := by
    rcases h8711 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1435 := by
    rcases h8716 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1436 := by
    rcases h8721 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8613 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21568 (p161 p1225 p1432 p1433 p1434 p1435 p1436 p1438 : Prop)
    (h8702 : p1432 ∨ p1438)
    (h8707 : p1433 ∨ p1438)
    (h8712 : p1434 ∨ p1438)
    (h8717 : p1435 ∨ p1438)
    (h8722 : p1436 ∨ p1438)
    (h8613 : p161 ∨ p1225 ∨ (¬ p1432) ∨ (¬ p1433) ∨ (¬ p1434) ∨ (¬ p1435) ∨ (¬ p1436)) : p1438 ∨ p161 ∨ p1225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1438) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p161) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1225) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1432 := by
    rcases h8702 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1433 := by
    rcases h8707 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1434 := by
    rcases h8712 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1435 := by
    rcases h8717 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1436 := by
    rcases h8722 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8613 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21569 (p161 p1225 p1432 p1433 p1434 p1435 p1436 p1439 : Prop)
    (h8703 : p1432 ∨ p1439)
    (h8708 : p1433 ∨ p1439)
    (h8713 : p1434 ∨ p1439)
    (h8718 : p1435 ∨ p1439)
    (h8723 : p1436 ∨ p1439)
    (h8613 : p161 ∨ p1225 ∨ (¬ p1432) ∨ (¬ p1433) ∨ (¬ p1434) ∨ (¬ p1435) ∨ (¬ p1436)) : p1439 ∨ p161 ∨ p1225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1439) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p161) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1225) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1432 := by
    rcases h8703 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1433 := by
    rcases h8708 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1434 := by
    rcases h8713 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1435 := by
    rcases h8718 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1436 := by
    rcases h8723 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8613 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21570 (p161 p1225 p1432 p1433 p1434 p1435 p1436 p1440 : Prop)
    (h8704 : p1432 ∨ p1440)
    (h8709 : p1433 ∨ p1440)
    (h8714 : p1434 ∨ p1440)
    (h8719 : p1435 ∨ p1440)
    (h8724 : p1436 ∨ p1440)
    (h8613 : p161 ∨ p1225 ∨ (¬ p1432) ∨ (¬ p1433) ∨ (¬ p1434) ∨ (¬ p1435) ∨ (¬ p1436)) : p1440 ∨ p161 ∨ p1225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1440) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p161) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1225) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1432 := by
    rcases h8704 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1433 := by
    rcases h8709 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1434 := by
    rcases h8714 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1435 := by
    rcases h8719 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1436 := by
    rcases h8724 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8613 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21571 (p161 p1225 p1432 p1433 p1434 p1435 p1436 p1437 p1438 p1439 p1440 p1441 : Prop)
    (h8638 : p161 ∨ p1225 ∨ (¬ p1437) ∨ (¬ p1438) ∨ (¬ p1439) ∨ (¬ p1440) ∨ (¬ p1441))
    (h8705 : p1432 ∨ p1441)
    (h8710 : p1433 ∨ p1441)
    (h8715 : p1434 ∨ p1441)
    (h8720 : p1435 ∨ p1441)
    (h8725 : p1436 ∨ p1441)
    (h8613 : p161 ∨ p1225 ∨ (¬ p1432) ∨ (¬ p1433) ∨ (¬ p1434) ∨ (¬ p1435) ∨ (¬ p1436)) : (¬ p1440) ∨ (¬ p1439) ∨ p161 ∨ p1225 ∨ (¬ p1437) ∨ (¬ p1438) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1440 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1439 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p161) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1437 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1441) := by
    rcases h8638 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p1432 := by
    rcases h8705 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1433 := by
    rcases h8710 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1434 := by
    rcases h8715 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1435 := by
    rcases h8720 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1436 := by
    rcases h8725 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h8613 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21572 (p161 p1225 p1437 p1438 p1439 p1440 : Prop)
    (h21567 : p1437 ∨ p161 ∨ p1225)
    (h21568 : p1438 ∨ p161 ∨ p1225)
    (h21569 : p1439 ∨ p161 ∨ p1225)
    (h21570 : p1440 ∨ p161 ∨ p1225)
    (h21571 : (¬ p1440) ∨ (¬ p1439) ∨ p161 ∨ p1225 ∨ (¬ p1437) ∨ (¬ p1438)) : p161 ∨ p1225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p161) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1225) := fun hu => hn (Or.inr hu)
  have u2 : p1437 := by
    rcases h21567 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1438 := by
    rcases h21568 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1439 := by
    rcases h21569 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1440 := by
    rcases h21570 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21571 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21573 (p422 p1256 p1259 p1260 p1261 p1262 p1263 p1264 : Prop)
    (h7557 : p1259 ∨ p1264)
    (h7562 : p1260 ∨ p1264)
    (h7567 : p1261 ∨ p1264)
    (h7572 : p1262 ∨ p1264)
    (h7577 : p1263 ∨ p1264)
    (h7469 : p422 ∨ p1256 ∨ (¬ p1259) ∨ (¬ p1260) ∨ (¬ p1261) ∨ (¬ p1262) ∨ (¬ p1263)) : p1264 ∨ p1256 ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1264) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1256) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p422) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1259 := by
    rcases h7557 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1260 := by
    rcases h7562 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1261 := by
    rcases h7567 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1262 := by
    rcases h7572 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1263 := by
    rcases h7577 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7469 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21574 (p422 p1256 p1259 p1260 p1261 p1262 p1263 p1265 : Prop)
    (h7558 : p1259 ∨ p1265)
    (h7563 : p1260 ∨ p1265)
    (h7568 : p1261 ∨ p1265)
    (h7573 : p1262 ∨ p1265)
    (h7578 : p1263 ∨ p1265)
    (h7469 : p422 ∨ p1256 ∨ (¬ p1259) ∨ (¬ p1260) ∨ (¬ p1261) ∨ (¬ p1262) ∨ (¬ p1263)) : p1265 ∨ p1256 ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1265) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1256) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p422) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1259 := by
    rcases h7558 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1260 := by
    rcases h7563 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1261 := by
    rcases h7568 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1262 := by
    rcases h7573 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1263 := by
    rcases h7578 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7469 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21575 (p422 p1256 p1259 p1260 p1261 p1262 p1263 p1266 : Prop)
    (h7559 : p1259 ∨ p1266)
    (h7564 : p1260 ∨ p1266)
    (h7569 : p1261 ∨ p1266)
    (h7574 : p1262 ∨ p1266)
    (h7579 : p1263 ∨ p1266)
    (h7469 : p422 ∨ p1256 ∨ (¬ p1259) ∨ (¬ p1260) ∨ (¬ p1261) ∨ (¬ p1262) ∨ (¬ p1263)) : p1266 ∨ p1256 ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1266) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1256) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p422) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1259 := by
    rcases h7559 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1260 := by
    rcases h7564 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1261 := by
    rcases h7569 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1262 := by
    rcases h7574 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1263 := by
    rcases h7579 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7469 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21576 (p422 p1256 p1259 p1260 p1261 p1262 p1263 p1267 : Prop)
    (h7560 : p1259 ∨ p1267)
    (h7565 : p1260 ∨ p1267)
    (h7570 : p1261 ∨ p1267)
    (h7575 : p1262 ∨ p1267)
    (h7580 : p1263 ∨ p1267)
    (h7469 : p422 ∨ p1256 ∨ (¬ p1259) ∨ (¬ p1260) ∨ (¬ p1261) ∨ (¬ p1262) ∨ (¬ p1263)) : p1267 ∨ p1256 ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1267) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1256) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p422) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h7469 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21578 (p422 p1250 p1259 p1260 p1261 p1262 p1263 p1268 : Prop)
    (h7561 : p1259 ∨ p1268)
    (h7566 : p1260 ∨ p1268)
    (h7571 : p1261 ∨ p1268)
    (h7576 : p1262 ∨ p1268)
    (h7581 : p1263 ∨ p1268)
    (h7468 : p422 ∨ p1250 ∨ (¬ p1259) ∨ (¬ p1260) ∨ (¬ p1261) ∨ (¬ p1262) ∨ (¬ p1263)) : p1268 ∨ p1250 ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1268) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1250) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p422) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1259 := by
    rcases h7561 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1260 := by
    rcases h7566 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1261 := by
    rcases h7571 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1262 := by
    rcases h7576 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1263 := by
    rcases h7581 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7468 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21579 (p422 p1250 p1259 p1264 p1265 p1266 p1267 p1268 : Prop)
    (h21578 : p1268 ∨ p1250 ∨ p422)
    (h7557 : p1259 ∨ p1264)
    (h7558 : p1259 ∨ p1265)
    (h7559 : p1259 ∨ p1266)
    (h7560 : p1259 ∨ p1267)
    (h7493 : p422 ∨ p1250 ∨ (¬ p1264) ∨ (¬ p1265) ∨ (¬ p1266) ∨ (¬ p1267) ∨ (¬ p1268)) : p1259 ∨ p1250 ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1259) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1250) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p422) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1268 := by
    rcases h21578 with q0 | q1 | q2
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
  have u7 : p1267 := by
    rcases h7560 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7493 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step21580 (p422 p1250 p1260 p1264 p1265 p1266 p1267 p1268 : Prop)
    (h21578 : p1268 ∨ p1250 ∨ p422)
    (h7562 : p1260 ∨ p1264)
    (h7563 : p1260 ∨ p1265)
    (h7564 : p1260 ∨ p1266)
    (h7565 : p1260 ∨ p1267)
    (h7493 : p422 ∨ p1250 ∨ (¬ p1264) ∨ (¬ p1265) ∨ (¬ p1266) ∨ (¬ p1267) ∨ (¬ p1268)) : p1260 ∨ p1250 ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1260) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1250) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p422) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1268 := by
    rcases h21578 with q0 | q1 | q2
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
  have u7 : p1267 := by
    rcases h7565 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7493 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step21581 (p422 p1250 p1261 p1264 p1265 p1266 p1267 p1268 : Prop)
    (h21578 : p1268 ∨ p1250 ∨ p422)
    (h7567 : p1261 ∨ p1264)
    (h7568 : p1261 ∨ p1265)
    (h7569 : p1261 ∨ p1266)
    (h7570 : p1261 ∨ p1267)
    (h7493 : p422 ∨ p1250 ∨ (¬ p1264) ∨ (¬ p1265) ∨ (¬ p1266) ∨ (¬ p1267) ∨ (¬ p1268)) : p1261 ∨ p1250 ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1261) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1250) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p422) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1268 := by
    rcases h21578 with q0 | q1 | q2
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
  have u7 : p1267 := by
    rcases h7570 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7493 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step21582 (p422 p1250 p1262 p1264 p1265 p1266 p1267 p1268 : Prop)
    (h21578 : p1268 ∨ p1250 ∨ p422)
    (h7572 : p1262 ∨ p1264)
    (h7573 : p1262 ∨ p1265)
    (h7574 : p1262 ∨ p1266)
    (h7575 : p1262 ∨ p1267)
    (h7493 : p422 ∨ p1250 ∨ (¬ p1264) ∨ (¬ p1265) ∨ (¬ p1266) ∨ (¬ p1267) ∨ (¬ p1268)) : p1262 ∨ p1250 ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1262) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1250) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p422) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1268 := by
    rcases h21578 with q0 | q1 | q2
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
  have u7 : p1267 := by
    rcases h7575 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7493 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step21583 (p422 p1250 p1259 p1260 p1261 p1262 p1263 p1264 p1265 p1266 p1267 p1268 : Prop)
    (h21578 : p1268 ∨ p1250 ∨ p422)
    (h21579 : p1259 ∨ p1250 ∨ p422)
    (h21580 : p1260 ∨ p1250 ∨ p422)
    (h21581 : p1261 ∨ p1250 ∨ p422)
    (h21582 : p1262 ∨ p1250 ∨ p422)
    (h7468 : p422 ∨ p1250 ∨ (¬ p1259) ∨ (¬ p1260) ∨ (¬ p1261) ∨ (¬ p1262) ∨ (¬ p1263))
    (h7577 : p1263 ∨ p1264)
    (h7578 : p1263 ∨ p1265)
    (h7579 : p1263 ∨ p1266)
    (h7580 : p1263 ∨ p1267)
    (h7493 : p422 ∨ p1250 ∨ (¬ p1264) ∨ (¬ p1265) ∨ (¬ p1266) ∨ (¬ p1267) ∨ (¬ p1268)) : p1250 ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1250) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p422) := fun hu => hn (Or.inr hu)
  have u2 : p1268 := by
    rcases h21578 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1259 := by
    rcases h21579 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1260 := by
    rcases h21580 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1261 := by
    rcases h21581 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p1262 := by
    rcases h21582 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p1263) := by
    rcases h7468 with q0 | q1 | q2 | q3 | q4 | q5 | q6
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
  have u11 : p1267 := by
    rcases h7580 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h7493 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u2)

theorem step21584 (p10 p329 p332 p333 p334 p335 p336 p337 : Prop)
    (h1799 : p332 ∨ p337)
    (h1804 : p333 ∨ p337)
    (h1809 : p334 ∨ p337)
    (h1814 : p335 ∨ p337)
    (h1819 : p336 ∨ p337)
    (h1710 : p10 ∨ p329 ∨ (¬ p332) ∨ (¬ p333) ∨ (¬ p334) ∨ (¬ p335) ∨ (¬ p336)) : p337 ∨ p10 ∨ p329 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p337) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p10) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p329) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p332 := by
    rcases h1799 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p333 := by
    rcases h1804 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p334 := by
    rcases h1809 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p335 := by
    rcases h1814 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p336 := by
    rcases h1819 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1710 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21585 (p10 p329 p332 p333 p334 p335 p336 p338 : Prop)
    (h1800 : p332 ∨ p338)
    (h1805 : p333 ∨ p338)
    (h1810 : p334 ∨ p338)
    (h1815 : p335 ∨ p338)
    (h1820 : p336 ∨ p338)
    (h1710 : p10 ∨ p329 ∨ (¬ p332) ∨ (¬ p333) ∨ (¬ p334) ∨ (¬ p335) ∨ (¬ p336)) : p338 ∨ p10 ∨ p329 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p338) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p10) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p329) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p332 := by
    rcases h1800 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p333 := by
    rcases h1805 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p334 := by
    rcases h1810 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p335 := by
    rcases h1815 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p336 := by
    rcases h1820 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1710 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21586 (p10 p329 p332 p333 p334 p335 p336 p339 : Prop)
    (h1801 : p332 ∨ p339)
    (h1806 : p333 ∨ p339)
    (h1811 : p334 ∨ p339)
    (h1816 : p335 ∨ p339)
    (h1821 : p336 ∨ p339)
    (h1710 : p10 ∨ p329 ∨ (¬ p332) ∨ (¬ p333) ∨ (¬ p334) ∨ (¬ p335) ∨ (¬ p336)) : p339 ∨ p10 ∨ p329 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p339) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p10) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p329) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p332 := by
    rcases h1801 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p333 := by
    rcases h1806 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p334 := by
    rcases h1811 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p335 := by
    rcases h1816 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p336 := by
    rcases h1821 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1710 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21587 (p10 p329 p332 p333 p334 p335 p336 p340 : Prop)
    (h1802 : p332 ∨ p340)
    (h1807 : p333 ∨ p340)
    (h1812 : p334 ∨ p340)
    (h1817 : p335 ∨ p340)
    (h1822 : p336 ∨ p340)
    (h1710 : p10 ∨ p329 ∨ (¬ p332) ∨ (¬ p333) ∨ (¬ p334) ∨ (¬ p335) ∨ (¬ p336)) : p340 ∨ p10 ∨ p329 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p340) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p10) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p329) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h1710 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21589 (p15 p68 p73 p74 p75 p76 p77 p81 : Prop)
    (h372 : p73 ∨ p81)
    (h377 : p74 ∨ p81)
    (h382 : p75 ∨ p81)
    (h387 : p76 ∨ p81)
    (h392 : p77 ∨ p81)
    (h276 : p15 ∨ p68 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77)) : p81 ∨ p68 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p81) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p68) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p73 := by
    rcases h372 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p74 := by
    rcases h377 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p75 := by
    rcases h382 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p76 := by
    rcases h387 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p77 := by
    rcases h392 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h276 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21590 (p1 p225 p540 p546 p547 p548 p549 p550 p551 p552 p553 p554 p555 : Prop)
    (h21061 : p551 ∨ p540 ∨ p1)
    (h21062 : p552 ∨ p540 ∨ p1)
    (h21063 : p553 ∨ p540 ∨ p1)
    (h21064 : p554 ∨ p540 ∨ p1)
    (h3023 : p1 ∨ p225 ∨ (¬ p551) ∨ (¬ p552) ∨ (¬ p553) ∨ (¬ p554) ∨ (¬ p555))
    (h3091 : p546 ∨ p555)
    (h3096 : p547 ∨ p555)
    (h3101 : p548 ∨ p555)
    (h3106 : p549 ∨ p555)
    (h3111 : p550 ∨ p555)
    (h2993 : p1 ∨ p540 ∨ (¬ p546) ∨ (¬ p547) ∨ (¬ p548) ∨ (¬ p549) ∨ (¬ p550)) : p1 ∨ p540 ∨ p225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p540) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p225) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p551 := by
    rcases h21061 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u4 : p552 := by
    rcases h21062 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u5 : p553 := by
    rcases h21063 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u6 : p554 := by
    rcases h21064 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u7 : (¬ p555) := by
    rcases h3023 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u0 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p546 := by
    rcases h3091 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p547 := by
    rcases h3096 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p548 := by
    rcases h3101 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p549 := by
    rcases h3106 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u12 : p550 := by
    rcases h3111 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h2993 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u12)

theorem step21591 (p15 p68 p73 p74 p75 p76 p77 p82 : Prop)
    (h373 : p73 ∨ p82)
    (h378 : p74 ∨ p82)
    (h383 : p75 ∨ p82)
    (h388 : p76 ∨ p82)
    (h393 : p77 ∨ p82)
    (h276 : p15 ∨ p68 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77)) : p82 ∨ p68 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p82) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p68) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p73 := by
    rcases h373 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p74 := by
    rcases h378 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p75 := by
    rcases h383 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p76 := by
    rcases h388 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p77 := by
    rcases h393 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h276 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21592 (p15 p68 p73 p74 p75 p76 p77 p78 : Prop)
    (h369 : p73 ∨ p78)
    (h374 : p74 ∨ p78)
    (h379 : p75 ∨ p78)
    (h384 : p76 ∨ p78)
    (h389 : p77 ∨ p78)
    (h276 : p15 ∨ p68 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77)) : p78 ∨ p68 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p78) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p68) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h276 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21593 (p15 p68 p73 p74 p75 p76 p77 p79 : Prop)
    (h370 : p73 ∨ p79)
    (h375 : p74 ∨ p79)
    (h380 : p75 ∨ p79)
    (h385 : p76 ∨ p79)
    (h390 : p77 ∨ p79)
    (h276 : p15 ∨ p68 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77)) : p79 ∨ p68 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p79) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p68) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p73 := by
    rcases h370 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p74 := by
    rcases h375 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p75 := by
    rcases h380 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p76 := by
    rcases h385 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p77 := by
    rcases h390 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h276 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21594 (p15 p68 p73 p74 p75 p76 p77 p78 p79 p80 p81 p82 : Prop)
    (h301 : p15 ∨ p68 ∨ (¬ p78) ∨ (¬ p79) ∨ (¬ p80) ∨ (¬ p81) ∨ (¬ p82))
    (h371 : p73 ∨ p80)
    (h376 : p74 ∨ p80)
    (h381 : p75 ∨ p80)
    (h386 : p76 ∨ p80)
    (h391 : p77 ∨ p80)
    (h276 : p15 ∨ p68 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77)) : (¬ p79) ∨ p68 ∨ p15 ∨ (¬ p81) ∨ (¬ p78) ∨ (¬ p82) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p79 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p68) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p81 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p78 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p82 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p80) := by
    rcases h301 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u0)
    · exact q4
    · exact False.elim (q5 u3)
    · exact False.elim (q6 u5)
  have u7 : p73 := by
    rcases h371 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p74 := by
    rcases h376 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p75 := by
    rcases h381 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p76 := by
    rcases h386 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p77 := by
    rcases h391 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h276 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21595 (p15 p68 p78 p79 p81 p82 : Prop)
    (h21589 : p81 ∨ p68 ∨ p15)
    (h21591 : p82 ∨ p68 ∨ p15)
    (h21592 : p78 ∨ p68 ∨ p15)
    (h21593 : p79 ∨ p68 ∨ p15)
    (h21594 : (¬ p79) ∨ p68 ∨ p15 ∨ (¬ p81) ∨ (¬ p78) ∨ (¬ p82)) : p68 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p68) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr hu)
  have u2 : p81 := by
    rcases h21589 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p82 := by
    rcases h21591 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p78 := by
    rcases h21592 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p79 := by
    rcases h21593 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21594 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step21596 (p10 p323 p332 p333 p334 p335 p336 p341 : Prop)
    (h1803 : p332 ∨ p341)
    (h1808 : p333 ∨ p341)
    (h1813 : p334 ∨ p341)
    (h1818 : p335 ∨ p341)
    (h1823 : p336 ∨ p341)
    (h1711 : p10 ∨ p323 ∨ (¬ p332) ∨ (¬ p333) ∨ (¬ p334) ∨ (¬ p335) ∨ (¬ p336)) : p341 ∨ p10 ∨ p323 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p341) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p10) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p323) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p332 := by
    rcases h1803 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p333 := by
    rcases h1808 with q0 | q1
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
  rcases h1711 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21597 (p10 p323 p332 p337 p338 p339 p340 p341 : Prop)
    (h21596 : p341 ∨ p10 ∨ p323)
    (h1799 : p332 ∨ p337)
    (h1800 : p332 ∨ p338)
    (h1801 : p332 ∨ p339)
    (h1802 : p332 ∨ p340)
    (h1736 : p10 ∨ p323 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341)) : p332 ∨ p10 ∨ p323 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p332) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p10) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p323) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p341 := by
    rcases h21596 with q0 | q1 | q2
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
  have u7 : p340 := by
    rcases h1802 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1736 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step21598 (p10 p323 p333 p337 p338 p339 p340 p341 : Prop)
    (h21596 : p341 ∨ p10 ∨ p323)
    (h1804 : p333 ∨ p337)
    (h1805 : p333 ∨ p338)
    (h1806 : p333 ∨ p339)
    (h1807 : p333 ∨ p340)
    (h1736 : p10 ∨ p323 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341)) : p333 ∨ p10 ∨ p323 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p333) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p10) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p323) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p341 := by
    rcases h21596 with q0 | q1 | q2
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
  have u7 : p340 := by
    rcases h1807 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1736 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step21599 (p10 p323 p334 p337 p338 p339 p340 p341 : Prop)
    (h21596 : p341 ∨ p10 ∨ p323)
    (h1809 : p334 ∨ p337)
    (h1810 : p334 ∨ p338)
    (h1811 : p334 ∨ p339)
    (h1812 : p334 ∨ p340)
    (h1736 : p10 ∨ p323 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341)) : p334 ∨ p10 ∨ p323 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p334) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p10) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p323) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p341 := by
    rcases h21596 with q0 | q1 | q2
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
  have u7 : p340 := by
    rcases h1812 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1736 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step21600 (p10 p323 p335 p337 p338 p339 p340 p341 : Prop)
    (h21596 : p341 ∨ p10 ∨ p323)
    (h1814 : p335 ∨ p337)
    (h1815 : p335 ∨ p338)
    (h1816 : p335 ∨ p339)
    (h1817 : p335 ∨ p340)
    (h1736 : p10 ∨ p323 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341)) : p335 ∨ p10 ∨ p323 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p335) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p10) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p323) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p341 := by
    rcases h21596 with q0 | q1 | q2
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
  have u7 : p340 := by
    rcases h1817 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1736 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step21602 (p323 p325 p336 p337 p338 p339 p340 p341 : Prop)
    (h1819 : p336 ∨ p337)
    (h1820 : p336 ∨ p338)
    (h1821 : p336 ∨ p339)
    (h1822 : p336 ∨ p340)
    (h1731 : p323 ∨ p325 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341)) : p336 ∨ (¬ p341) ∨ p323 ∨ p325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p336) := fun hu => hn (Or.inl hu)
  have u1 : p341 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p323) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p325) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  have u7 : p340 := by
    rcases h1822 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1731 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21603 (p325 p329 p332 p333 p334 p335 p336 p337 : Prop)
    (h1799 : p332 ∨ p337)
    (h1804 : p333 ∨ p337)
    (h1809 : p334 ∨ p337)
    (h1814 : p335 ∨ p337)
    (h1705 : p325 ∨ p329 ∨ (¬ p332) ∨ (¬ p333) ∨ (¬ p334) ∨ (¬ p335) ∨ (¬ p336)) : p337 ∨ (¬ p336) ∨ p329 ∨ p325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p337) := fun hu => hn (Or.inl hu)
  have u1 : p336 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p329) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p325) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p332 := by
    rcases h1799 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p333 := by
    rcases h1804 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p334 := by
    rcases h1809 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p335 := by
    rcases h1814 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1705 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21604 (p325 p329 p332 p333 p334 p335 p336 p338 : Prop)
    (h1800 : p332 ∨ p338)
    (h1805 : p333 ∨ p338)
    (h1810 : p334 ∨ p338)
    (h1815 : p335 ∨ p338)
    (h1705 : p325 ∨ p329 ∨ (¬ p332) ∨ (¬ p333) ∨ (¬ p334) ∨ (¬ p335) ∨ (¬ p336)) : p338 ∨ (¬ p336) ∨ p329 ∨ p325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p338) := fun hu => hn (Or.inl hu)
  have u1 : p336 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p329) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p325) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p332 := by
    rcases h1800 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p333 := by
    rcases h1805 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p334 := by
    rcases h1810 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p335 := by
    rcases h1815 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1705 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21605 (p325 p329 p332 p333 p334 p335 p336 p339 : Prop)
    (h1801 : p332 ∨ p339)
    (h1806 : p333 ∨ p339)
    (h1811 : p334 ∨ p339)
    (h1816 : p335 ∨ p339)
    (h1705 : p325 ∨ p329 ∨ (¬ p332) ∨ (¬ p333) ∨ (¬ p334) ∨ (¬ p335) ∨ (¬ p336)) : p339 ∨ (¬ p336) ∨ p329 ∨ p325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p339) := fun hu => hn (Or.inl hu)
  have u1 : p336 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p329) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p325) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p332 := by
    rcases h1801 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p333 := by
    rcases h1806 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p334 := by
    rcases h1811 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p335 := by
    rcases h1816 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1705 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21606 (p323 p325 p329 p332 p333 p334 p335 p336 p337 p338 p339 p340 p341 : Prop)
    (h21602 : p336 ∨ (¬ p341) ∨ p323 ∨ p325)
    (h21603 : p337 ∨ (¬ p336) ∨ p329 ∨ p325)
    (h21604 : p338 ∨ (¬ p336) ∨ p329 ∨ p325)
    (h21605 : p339 ∨ (¬ p336) ∨ p329 ∨ p325)
    (h1731 : p323 ∨ p325 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341))
    (h1802 : p332 ∨ p340)
    (h1807 : p333 ∨ p340)
    (h1812 : p334 ∨ p340)
    (h1817 : p335 ∨ p340)
    (h1705 : p325 ∨ p329 ∨ (¬ p332) ∨ (¬ p333) ∨ (¬ p334) ∨ (¬ p335) ∨ (¬ p336)) : (¬ p341) ∨ p329 ∨ p323 ∨ p325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p341 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p329) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p323) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p325) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p336 := by
    rcases h21602 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u2 q2)
    · exact False.elim (u3 q3)
  have u5 : p337 := by
    rcases h21603 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u4)
    · exact False.elim (u1 q2)
    · exact False.elim (u3 q3)
  have u6 : p338 := by
    rcases h21604 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u4)
    · exact False.elim (u1 q2)
    · exact False.elim (u3 q3)
  have u7 : p339 := by
    rcases h21605 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u4)
    · exact False.elim (u1 q2)
    · exact False.elim (u3 q3)
  have u8 : (¬ p340) := by
    rcases h1731 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u6)
    · exact False.elim (q4 u7)
    · exact q5
    · exact False.elim (q6 u0)
  have u9 : p332 := by
    rcases h1802 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u10 : p333 := by
    rcases h1807 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u11 : p334 := by
    rcases h1812 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u12 : p335 := by
    rcases h1817 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h1705 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u12)
  · exact False.elim (q6 u4)

theorem step21607 (p323 p325 p329 p332 p333 p334 p335 p336 p341 : Prop)
    (h21606 : (¬ p341) ∨ p329 ∨ p323 ∨ p325)
    (h1803 : p332 ∨ p341)
    (h1808 : p333 ∨ p341)
    (h1813 : p334 ∨ p341)
    (h1818 : p335 ∨ p341)
    (h1823 : p336 ∨ p341)
    (h1705 : p325 ∨ p329 ∨ (¬ p332) ∨ (¬ p333) ∨ (¬ p334) ∨ (¬ p335) ∨ (¬ p336)) : p329 ∨ p323 ∨ p325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p329) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p323) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p325) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : (¬ p341) := by
    rcases h21606 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u4 : p332 := by
    rcases h1803 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u5 : p333 := by
    rcases h1808 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p334 := by
    rcases h1813 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p335 := by
    rcases h1818 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p336 := by
    rcases h1823 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h1705 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u8)

theorem step21609 (p10 p329 p332 p333 p334 p335 p336 p337 p338 p339 p340 p341 : Prop)
    (h1735 : p10 ∨ p329 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341))
    (h1803 : p332 ∨ p341)
    (h1808 : p333 ∨ p341)
    (h1813 : p334 ∨ p341)
    (h1818 : p335 ∨ p341)
    (h1823 : p336 ∨ p341)
    (h1710 : p10 ∨ p329 ∨ (¬ p332) ∨ (¬ p333) ∨ (¬ p334) ∨ (¬ p335) ∨ (¬ p336)) : (¬ p340) ∨ (¬ p339) ∨ p329 ∨ p10 ∨ (¬ p337) ∨ (¬ p338) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p340 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p339 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p329) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p337 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p338 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p341) := by
    rcases h1735 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p332 := by
    rcases h1803 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p333 := by
    rcases h1808 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p334 := by
    rcases h1813 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p335 := by
    rcases h1818 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p336 := by
    rcases h1823 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h1710 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21610 (p10 p329 p337 p338 p339 p340 : Prop)
    (h21584 : p337 ∨ p10 ∨ p329)
    (h21585 : p338 ∨ p10 ∨ p329)
    (h21586 : p339 ∨ p10 ∨ p329)
    (h21587 : p340 ∨ p10 ∨ p329)
    (h21609 : (¬ p340) ∨ (¬ p339) ∨ p329 ∨ p10 ∨ (¬ p337) ∨ (¬ p338)) : p329 ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p329) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p10) := fun hu => hn (Or.inr hu)
  have u2 : p337 := by
    rcases h21584 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u3 : p338 := by
    rcases h21585 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u4 : p339 := by
    rcases h21586 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u5 : p340 := by
    rcases h21587 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  rcases h21609 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21612 (p1 p225 p546 p547 p548 p549 p550 p555 : Prop)
    (h3091 : p546 ∨ p555)
    (h3096 : p547 ∨ p555)
    (h3101 : p548 ∨ p555)
    (h3106 : p549 ∨ p555)
    (h3111 : p550 ∨ p555)
    (h2998 : p1 ∨ p225 ∨ (¬ p546) ∨ (¬ p547) ∨ (¬ p548) ∨ (¬ p549) ∨ (¬ p550)) : p555 ∨ p1 ∨ p225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p555) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p225) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p546 := by
    rcases h3091 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p547 := by
    rcases h3096 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p548 := by
    rcases h3101 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p549 := by
    rcases h3106 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p550 := by
    rcases h3111 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2998 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21613 (p1 p225 p546 p551 p552 p553 p554 p555 : Prop)
    (h21612 : p555 ∨ p1 ∨ p225)
    (h3087 : p546 ∨ p551)
    (h3088 : p546 ∨ p552)
    (h3089 : p546 ∨ p553)
    (h3090 : p546 ∨ p554)
    (h3023 : p1 ∨ p225 ∨ (¬ p551) ∨ (¬ p552) ∨ (¬ p553) ∨ (¬ p554) ∨ (¬ p555)) : p546 ∨ p1 ∨ p225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p546) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p225) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p555 := by
    rcases h21612 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p551 := by
    rcases h3087 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p552 := by
    rcases h3088 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p553 := by
    rcases h3089 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p554 := by
    rcases h3090 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3023 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step21614 (p1 p225 p547 p551 p552 p553 p554 p555 : Prop)
    (h21612 : p555 ∨ p1 ∨ p225)
    (h3092 : p547 ∨ p551)
    (h3093 : p547 ∨ p552)
    (h3094 : p547 ∨ p553)
    (h3095 : p547 ∨ p554)
    (h3023 : p1 ∨ p225 ∨ (¬ p551) ∨ (¬ p552) ∨ (¬ p553) ∨ (¬ p554) ∨ (¬ p555)) : p547 ∨ p1 ∨ p225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p547) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p225) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p555 := by
    rcases h21612 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p551 := by
    rcases h3092 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p552 := by
    rcases h3093 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p553 := by
    rcases h3094 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p554 := by
    rcases h3095 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3023 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step21615 (p1 p225 p548 p551 p552 p553 p554 p555 : Prop)
    (h21612 : p555 ∨ p1 ∨ p225)
    (h3097 : p548 ∨ p551)
    (h3098 : p548 ∨ p552)
    (h3099 : p548 ∨ p553)
    (h3100 : p548 ∨ p554)
    (h3023 : p1 ∨ p225 ∨ (¬ p551) ∨ (¬ p552) ∨ (¬ p553) ∨ (¬ p554) ∨ (¬ p555)) : p548 ∨ p1 ∨ p225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p548) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p225) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p555 := by
    rcases h21612 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p551 := by
    rcases h3097 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p552 := by
    rcases h3098 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p553 := by
    rcases h3099 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p554 := by
    rcases h3100 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3023 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step21616 (p1 p225 p549 p551 p552 p553 p554 p555 : Prop)
    (h21612 : p555 ∨ p1 ∨ p225)
    (h3102 : p549 ∨ p551)
    (h3103 : p549 ∨ p552)
    (h3104 : p549 ∨ p553)
    (h3105 : p549 ∨ p554)
    (h3023 : p1 ∨ p225 ∨ (¬ p551) ∨ (¬ p552) ∨ (¬ p553) ∨ (¬ p554) ∨ (¬ p555)) : p549 ∨ p1 ∨ p225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p549) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p225) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p555 := by
    rcases h21612 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p551 := by
    rcases h3102 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p552 := by
    rcases h3103 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p553 := by
    rcases h3104 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p554 := by
    rcases h3105 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3023 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step21617 (p1 p225 p546 p547 p548 p549 p550 p551 p552 p553 p554 p555 : Prop)
    (h21612 : p555 ∨ p1 ∨ p225)
    (h21613 : p546 ∨ p1 ∨ p225)
    (h21614 : p547 ∨ p1 ∨ p225)
    (h21615 : p548 ∨ p1 ∨ p225)
    (h21616 : p549 ∨ p1 ∨ p225)
    (h2998 : p1 ∨ p225 ∨ (¬ p546) ∨ (¬ p547) ∨ (¬ p548) ∨ (¬ p549) ∨ (¬ p550))
    (h3107 : p550 ∨ p551)
    (h3108 : p550 ∨ p552)
    (h3109 : p550 ∨ p553)
    (h3110 : p550 ∨ p554)
    (h3023 : p1 ∨ p225 ∨ (¬ p551) ∨ (¬ p552) ∨ (¬ p553) ∨ (¬ p554) ∨ (¬ p555)) : p1 ∨ p225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr hu)
  have u2 : p555 := by
    rcases h21612 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p546 := by
    rcases h21613 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p547 := by
    rcases h21614 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p548 := by
    rcases h21615 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p549 := by
    rcases h21616 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p550) := by
    rcases h2998 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u0 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p551 := by
    rcases h3107 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p552 := by
    rcases h3108 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p553 := by
    rcases h3109 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p554 := by
    rcases h3110 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h3023 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u2)

theorem step21618 (p101 p102 p111 p116 p117 p118 p119 p120 : Prop)
    (h620 : p111 ∨ p116)
    (h621 : p111 ∨ p117)
    (h622 : p111 ∨ p118)
    (h623 : p111 ∨ p119)
    (h624 : p111 ∨ p120)
    (h557 : p101 ∨ p102 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p111 ∨ p101 ∨ p102 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p111) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p101) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p102) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p116 := by
    rcases h620 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p117 := by
    rcases h621 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p118 := by
    rcases h622 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p119 := by
    rcases h623 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p120 := by
    rcases h624 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h557 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21619 (p101 p102 p112 p116 p117 p118 p119 p120 : Prop)
    (h625 : p112 ∨ p116)
    (h626 : p112 ∨ p117)
    (h627 : p112 ∨ p118)
    (h628 : p112 ∨ p119)
    (h629 : p112 ∨ p120)
    (h557 : p101 ∨ p102 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p112 ∨ p101 ∨ p102 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p112) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p101) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p102) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p116 := by
    rcases h625 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p117 := by
    rcases h626 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p118 := by
    rcases h627 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p119 := by
    rcases h628 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p120 := by
    rcases h629 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h557 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21620 (p101 p102 p113 p116 p117 p118 p119 p120 : Prop)
    (h630 : p113 ∨ p116)
    (h631 : p113 ∨ p117)
    (h632 : p113 ∨ p118)
    (h633 : p113 ∨ p119)
    (h634 : p113 ∨ p120)
    (h557 : p101 ∨ p102 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p113 ∨ p101 ∨ p102 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p113) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p101) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p102) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p116 := by
    rcases h630 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p117 := by
    rcases h631 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p118 := by
    rcases h632 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p119 := by
    rcases h633 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p120 := by
    rcases h634 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h557 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21621 (p101 p102 p114 p116 p117 p118 p119 p120 : Prop)
    (h635 : p114 ∨ p116)
    (h636 : p114 ∨ p117)
    (h637 : p114 ∨ p118)
    (h638 : p114 ∨ p119)
    (h639 : p114 ∨ p120)
    (h557 : p101 ∨ p102 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p114 ∨ p101 ∨ p102 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p114) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p101) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p102) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p116 := by
    rcases h635 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p117 := by
    rcases h636 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p118 := by
    rcases h637 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p119 := by
    rcases h638 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p120 := by
    rcases h639 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h557 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21622 (p101 p102 p111 p112 p113 p114 p115 p116 p117 p118 p119 p120 : Prop)
    (h532 : p101 ∨ p102 ∨ (¬ p111) ∨ (¬ p112) ∨ (¬ p113) ∨ (¬ p114) ∨ (¬ p115))
    (h640 : p115 ∨ p116)
    (h641 : p115 ∨ p117)
    (h642 : p115 ∨ p118)
    (h643 : p115 ∨ p119)
    (h644 : p115 ∨ p120)
    (h557 : p101 ∨ p102 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : (¬ p114) ∨ (¬ p113) ∨ (¬ p111) ∨ p102 ∨ p101 ∨ (¬ p112) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p114 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p113 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p111 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p102) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p112 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p115) := by
    rcases h532 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u4 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u2)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p116 := by
    rcases h640 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p117 := by
    rcases h641 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p118 := by
    rcases h642 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p119 := by
    rcases h643 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p120 := by
    rcases h644 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h557 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21623 (p101 p102 p111 p112 p113 p114 : Prop)
    (h21618 : p111 ∨ p101 ∨ p102)
    (h21619 : p112 ∨ p101 ∨ p102)
    (h21620 : p113 ∨ p101 ∨ p102)
    (h21621 : p114 ∨ p101 ∨ p102)
    (h21622 : (¬ p114) ∨ (¬ p113) ∨ (¬ p111) ∨ p102 ∨ p101 ∨ (¬ p112)) : p101 ∨ p102 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p101) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p102) := fun hu => hn (Or.inr hu)
  have u2 : p111 := by
    rcases h21618 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p112 := by
    rcases h21619 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p113 := by
    rcases h21620 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p114 := by
    rcases h21621 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21622 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (u1 q3)
  · exact False.elim (u0 q4)
  · exact False.elim (q5 u3)

theorem step21624 (p1206 p1211 p1215 p1216 p1217 p1218 p1219 p1223 : Prop)
    (h7301 : p1215 ∨ p1223)
    (h7306 : p1216 ∨ p1223)
    (h7311 : p1217 ∨ p1223)
    (h7316 : p1218 ∨ p1223)
    (h7321 : p1219 ∨ p1223)
    (h7208 : p1206 ∨ p1211 ∨ (¬ p1215) ∨ (¬ p1216) ∨ (¬ p1217) ∨ (¬ p1218) ∨ (¬ p1219)) : p1223 ∨ p1211 ∨ p1206 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1223) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1211) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h7208 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21625 (p1207 p1211 p1215 p1220 p1221 p1222 p1223 p1224 : Prop)
    (h7298 : p1215 ∨ p1220)
    (h7299 : p1215 ∨ p1221)
    (h7300 : p1215 ∨ p1222)
    (h7302 : p1215 ∨ p1224)
    (h7223 : p1207 ∨ p1211 ∨ (¬ p1220) ∨ (¬ p1221) ∨ (¬ p1222) ∨ (¬ p1223) ∨ (¬ p1224)) : p1215 ∨ (¬ p1223) ∨ p1211 ∨ p1207 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1215) := fun hu => hn (Or.inl hu)
  have u1 : p1223 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1211) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1207) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h7223 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step21626 (p1207 p1211 p1216 p1220 p1221 p1222 p1223 p1224 : Prop)
    (h7303 : p1216 ∨ p1220)
    (h7304 : p1216 ∨ p1221)
    (h7305 : p1216 ∨ p1222)
    (h7307 : p1216 ∨ p1224)
    (h7223 : p1207 ∨ p1211 ∨ (¬ p1220) ∨ (¬ p1221) ∨ (¬ p1222) ∨ (¬ p1223) ∨ (¬ p1224)) : p1216 ∨ (¬ p1223) ∨ p1211 ∨ p1207 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1216) := fun hu => hn (Or.inl hu)
  have u1 : p1223 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1211) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1207) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h7223 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step21627 (p1207 p1211 p1217 p1220 p1221 p1222 p1223 p1224 : Prop)
    (h7308 : p1217 ∨ p1220)
    (h7309 : p1217 ∨ p1221)
    (h7310 : p1217 ∨ p1222)
    (h7312 : p1217 ∨ p1224)
    (h7223 : p1207 ∨ p1211 ∨ (¬ p1220) ∨ (¬ p1221) ∨ (¬ p1222) ∨ (¬ p1223) ∨ (¬ p1224)) : p1217 ∨ (¬ p1223) ∨ p1211 ∨ p1207 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1217) := fun hu => hn (Or.inl hu)
  have u1 : p1223 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1211) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1207) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h7223 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step21628 (p1207 p1211 p1218 p1220 p1221 p1222 p1223 p1224 : Prop)
    (h7313 : p1218 ∨ p1220)
    (h7314 : p1218 ∨ p1221)
    (h7315 : p1218 ∨ p1222)
    (h7317 : p1218 ∨ p1224)
    (h7223 : p1207 ∨ p1211 ∨ (¬ p1220) ∨ (¬ p1221) ∨ (¬ p1222) ∨ (¬ p1223) ∨ (¬ p1224)) : p1218 ∨ (¬ p1223) ∨ p1211 ∨ p1207 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1218) := fun hu => hn (Or.inl hu)
  have u1 : p1223 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1211) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1207) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h7223 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step21629 (p1206 p1207 p1211 p1215 p1216 p1217 p1218 p1219 p1220 p1221 p1222 p1223 p1224 : Prop)
    (h21624 : p1223 ∨ p1211 ∨ p1206)
    (h21625 : p1215 ∨ (¬ p1223) ∨ p1211 ∨ p1207)
    (h21626 : p1216 ∨ (¬ p1223) ∨ p1211 ∨ p1207)
    (h21627 : p1217 ∨ (¬ p1223) ∨ p1211 ∨ p1207)
    (h21628 : p1218 ∨ (¬ p1223) ∨ p1211 ∨ p1207)
    (h7208 : p1206 ∨ p1211 ∨ (¬ p1215) ∨ (¬ p1216) ∨ (¬ p1217) ∨ (¬ p1218) ∨ (¬ p1219))
    (h7318 : p1219 ∨ p1220)
    (h7319 : p1219 ∨ p1221)
    (h7320 : p1219 ∨ p1222)
    (h7322 : p1219 ∨ p1224)
    (h7223 : p1207 ∨ p1211 ∨ (¬ p1220) ∨ (¬ p1221) ∨ (¬ p1222) ∨ (¬ p1223) ∨ (¬ p1224)) : p1211 ∨ p1207 ∨ p1206 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1211) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1207) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1206) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1223 := by
    rcases h21624 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u4 : p1215 := by
    rcases h21625 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u0 q2)
    · exact False.elim (u1 q3)
  have u5 : p1216 := by
    rcases h21626 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u0 q2)
    · exact False.elim (u1 q3)
  have u6 : p1217 := by
    rcases h21627 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u0 q2)
    · exact False.elim (u1 q3)
  have u7 : p1218 := by
    rcases h21628 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u0 q2)
    · exact False.elim (u1 q3)
  have u8 : (¬ p1219) := by
    rcases h7208 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u6)
    · exact False.elim (q5 u7)
    · exact q6
  have u9 : p1220 := by
    rcases h7318 with q0 | q1
    · exact False.elim (u8 q0)
    · exact q1
  have u10 : p1221 := by
    rcases h7319 with q0 | q1
    · exact False.elim (u8 q0)
    · exact q1
  have u11 : p1222 := by
    rcases h7320 with q0 | q1
    · exact False.elim (u8 q0)
    · exact q1
  have u12 : p1224 := by
    rcases h7322 with q0 | q1
    · exact False.elim (u8 q0)
    · exact q1
  rcases h7223 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u12)

theorem step21630 (p1078 p1084 p1085 p1090 p1091 p1092 p1093 p1094 : Prop)
    (h6450 : p1085 ∨ p1090)
    (h6451 : p1085 ∨ p1091)
    (h6452 : p1085 ∨ p1092)
    (h6453 : p1085 ∨ p1093)
    (h6454 : p1085 ∨ p1094)
    (h6378 : p1078 ∨ p1084 ∨ (¬ p1090) ∨ (¬ p1091) ∨ (¬ p1092) ∨ (¬ p1093) ∨ (¬ p1094)) : p1085 ∨ p1084 ∨ p1078 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1085) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1084) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1078) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1090 := by
    rcases h6450 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1091 := by
    rcases h6451 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1092 := by
    rcases h6452 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1093 := by
    rcases h6453 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1094 := by
    rcases h6454 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6378 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21631 (p1078 p1084 p1086 p1090 p1091 p1092 p1093 p1094 : Prop)
    (h6455 : p1086 ∨ p1090)
    (h6456 : p1086 ∨ p1091)
    (h6457 : p1086 ∨ p1092)
    (h6458 : p1086 ∨ p1093)
    (h6459 : p1086 ∨ p1094)
    (h6378 : p1078 ∨ p1084 ∨ (¬ p1090) ∨ (¬ p1091) ∨ (¬ p1092) ∨ (¬ p1093) ∨ (¬ p1094)) : p1086 ∨ p1084 ∨ p1078 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1086) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1084) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1078) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1090 := by
    rcases h6455 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1091 := by
    rcases h6456 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1092 := by
    rcases h6457 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1093 := by
    rcases h6458 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1094 := by
    rcases h6459 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6378 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21632 (p1078 p1084 p1087 p1090 p1091 p1092 p1093 p1094 : Prop)
    (h6460 : p1087 ∨ p1090)
    (h6461 : p1087 ∨ p1091)
    (h6462 : p1087 ∨ p1092)
    (h6463 : p1087 ∨ p1093)
    (h6464 : p1087 ∨ p1094)
    (h6378 : p1078 ∨ p1084 ∨ (¬ p1090) ∨ (¬ p1091) ∨ (¬ p1092) ∨ (¬ p1093) ∨ (¬ p1094)) : p1087 ∨ p1084 ∨ p1078 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1087) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1084) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1078) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1090 := by
    rcases h6460 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1091 := by
    rcases h6461 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1092 := by
    rcases h6462 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1093 := by
    rcases h6463 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1094 := by
    rcases h6464 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6378 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21633 (p1078 p1084 p1088 p1090 p1091 p1092 p1093 p1094 : Prop)
    (h6465 : p1088 ∨ p1090)
    (h6466 : p1088 ∨ p1091)
    (h6467 : p1088 ∨ p1092)
    (h6468 : p1088 ∨ p1093)
    (h6469 : p1088 ∨ p1094)
    (h6378 : p1078 ∨ p1084 ∨ (¬ p1090) ∨ (¬ p1091) ∨ (¬ p1092) ∨ (¬ p1093) ∨ (¬ p1094)) : p1088 ∨ p1084 ∨ p1078 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1088) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1084) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1078) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h6378 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21634 (p1078 p1084 p1085 p1086 p1087 p1088 p1089 p1090 p1091 p1092 p1093 p1094 : Prop)
    (h6353 : p1078 ∨ p1084 ∨ (¬ p1085) ∨ (¬ p1086) ∨ (¬ p1087) ∨ (¬ p1088) ∨ (¬ p1089))
    (h6470 : p1089 ∨ p1090)
    (h6471 : p1089 ∨ p1091)
    (h6472 : p1089 ∨ p1092)
    (h6473 : p1089 ∨ p1093)
    (h6474 : p1089 ∨ p1094)
    (h6378 : p1078 ∨ p1084 ∨ (¬ p1090) ∨ (¬ p1091) ∨ (¬ p1092) ∨ (¬ p1093) ∨ (¬ p1094)) : (¬ p1088) ∨ (¬ p1087) ∨ p1078 ∨ p1084 ∨ (¬ p1085) ∨ (¬ p1086) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1088 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1087 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1078) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1084) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1085 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1086 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1089) := by
    rcases h6353 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p1090 := by
    rcases h6470 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1091 := by
    rcases h6471 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1092 := by
    rcases h6472 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1093 := by
    rcases h6473 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1094 := by
    rcases h6474 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h6378 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21635 (p1078 p1084 p1085 p1086 p1087 p1088 : Prop)
    (h21630 : p1085 ∨ p1084 ∨ p1078)
    (h21631 : p1086 ∨ p1084 ∨ p1078)
    (h21632 : p1087 ∨ p1084 ∨ p1078)
    (h21633 : p1088 ∨ p1084 ∨ p1078)
    (h21634 : (¬ p1088) ∨ (¬ p1087) ∨ p1078 ∨ p1084 ∨ (¬ p1085) ∨ (¬ p1086)) : p1084 ∨ p1078 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1084) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1078) := fun hu => hn (Or.inr hu)
  have u2 : p1085 := by
    rcases h21630 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1086 := by
    rcases h21631 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1087 := by
    rcases h21632 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1088 := by
    rcases h21633 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21634 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21636 (p422 p1256 p1259 p1260 p1261 p1262 p1263 p1264 p1265 p1266 p1267 p1268 : Prop)
    (h7494 : p422 ∨ p1256 ∨ (¬ p1264) ∨ (¬ p1265) ∨ (¬ p1266) ∨ (¬ p1267) ∨ (¬ p1268))
    (h7561 : p1259 ∨ p1268)
    (h7566 : p1260 ∨ p1268)
    (h7571 : p1261 ∨ p1268)
    (h7576 : p1262 ∨ p1268)
    (h7581 : p1263 ∨ p1268)
    (h7469 : p422 ∨ p1256 ∨ (¬ p1259) ∨ (¬ p1260) ∨ (¬ p1261) ∨ (¬ p1262) ∨ (¬ p1263)) : p1256 ∨ (¬ p1267) ∨ p422 ∨ (¬ p1266) ∨ (¬ p1264) ∨ (¬ p1265) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1256) := fun hu => hn (Or.inl hu)
  have u1 : p1267 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1264 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1268) := by
    rcases h7494 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u1)
    · exact q6
  have u7 : p1259 := by
    rcases h7561 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1260 := by
    rcases h7566 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1261 := by
    rcases h7571 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1262 := by
    rcases h7576 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1263 := by
    rcases h7581 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h7469 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21637 (p422 p1256 p1264 p1265 p1266 p1267 : Prop)
    (h21573 : p1264 ∨ p1256 ∨ p422)
    (h21574 : p1265 ∨ p1256 ∨ p422)
    (h21575 : p1266 ∨ p1256 ∨ p422)
    (h21576 : p1267 ∨ p1256 ∨ p422)
    (h21636 : p1256 ∨ (¬ p1267) ∨ p422 ∨ (¬ p1266) ∨ (¬ p1264) ∨ (¬ p1265)) : p1256 ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1256) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p422) := fun hu => hn (Or.inr hu)
  have u2 : p1264 := by
    rcases h21573 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1265 := by
    rcases h21574 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1266 := by
    rcases h21575 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1267 := by
    rcases h21576 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21636 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21639 (p1330 p1333 p1336 p1341 p1342 p1343 p1344 p1345 : Prop)
    (h8072 : p1336 ∨ p1341)
    (h8073 : p1336 ∨ p1342)
    (h8074 : p1336 ∨ p1343)
    (h8075 : p1336 ∨ p1344)
    (h8076 : p1336 ∨ p1345)
    (h8019 : p1330 ∨ p1333 ∨ (¬ p1341) ∨ (¬ p1342) ∨ (¬ p1343) ∨ (¬ p1344) ∨ (¬ p1345)) : p1336 ∨ p1330 ∨ p1333 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1336) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1330) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1333) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1341 := by
    rcases h8072 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1342 := by
    rcases h8073 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1343 := by
    rcases h8074 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1344 := by
    rcases h8075 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1345 := by
    rcases h8076 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8019 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21640 (p1330 p1333 p1337 p1341 p1342 p1343 p1344 p1345 : Prop)
    (h8077 : p1337 ∨ p1341)
    (h8078 : p1337 ∨ p1342)
    (h8079 : p1337 ∨ p1343)
    (h8080 : p1337 ∨ p1344)
    (h8081 : p1337 ∨ p1345)
    (h8019 : p1330 ∨ p1333 ∨ (¬ p1341) ∨ (¬ p1342) ∨ (¬ p1343) ∨ (¬ p1344) ∨ (¬ p1345)) : p1337 ∨ p1330 ∨ p1333 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1337) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1330) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1333) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1341 := by
    rcases h8077 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1342 := by
    rcases h8078 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1343 := by
    rcases h8079 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1344 := by
    rcases h8080 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1345 := by
    rcases h8081 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8019 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21641 (p1330 p1333 p1338 p1341 p1342 p1343 p1344 p1345 : Prop)
    (h8082 : p1338 ∨ p1341)
    (h8083 : p1338 ∨ p1342)
    (h8084 : p1338 ∨ p1343)
    (h8085 : p1338 ∨ p1344)
    (h8086 : p1338 ∨ p1345)
    (h8019 : p1330 ∨ p1333 ∨ (¬ p1341) ∨ (¬ p1342) ∨ (¬ p1343) ∨ (¬ p1344) ∨ (¬ p1345)) : p1338 ∨ p1330 ∨ p1333 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1338) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1330) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1333) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h8019 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21642 (p1330 p1333 p1339 p1341 p1342 p1343 p1344 p1345 : Prop)
    (h8087 : p1339 ∨ p1341)
    (h8088 : p1339 ∨ p1342)
    (h8089 : p1339 ∨ p1343)
    (h8090 : p1339 ∨ p1344)
    (h8091 : p1339 ∨ p1345)
    (h8019 : p1330 ∨ p1333 ∨ (¬ p1341) ∨ (¬ p1342) ∨ (¬ p1343) ∨ (¬ p1344) ∨ (¬ p1345)) : p1339 ∨ p1330 ∨ p1333 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1339) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1330) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1333) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1341 := by
    rcases h8087 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1342 := by
    rcases h8088 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1343 := by
    rcases h8089 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1344 := by
    rcases h8090 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1345 := by
    rcases h8091 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8019 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21643 (p1330 p1333 p1336 p1337 p1338 p1339 p1340 p1341 p1342 p1343 p1344 p1345 : Prop)
    (h7994 : p1330 ∨ p1333 ∨ (¬ p1336) ∨ (¬ p1337) ∨ (¬ p1338) ∨ (¬ p1339) ∨ (¬ p1340))
    (h8092 : p1340 ∨ p1341)
    (h8093 : p1340 ∨ p1342)
    (h8094 : p1340 ∨ p1343)
    (h8095 : p1340 ∨ p1344)
    (h8096 : p1340 ∨ p1345)
    (h8019 : p1330 ∨ p1333 ∨ (¬ p1341) ∨ (¬ p1342) ∨ (¬ p1343) ∨ (¬ p1344) ∨ (¬ p1345)) : (¬ p1339) ∨ (¬ p1338) ∨ p1333 ∨ p1330 ∨ (¬ p1336) ∨ (¬ p1337) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1339 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1338 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1333) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1330) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1336 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1337 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1340) := by
    rcases h7994 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p1341 := by
    rcases h8092 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1342 := by
    rcases h8093 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1343 := by
    rcases h8094 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1344 := by
    rcases h8095 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1345 := by
    rcases h8096 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h8019 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21644 (p1330 p1333 p1336 p1337 p1338 p1339 : Prop)
    (h21639 : p1336 ∨ p1330 ∨ p1333)
    (h21640 : p1337 ∨ p1330 ∨ p1333)
    (h21641 : p1338 ∨ p1330 ∨ p1333)
    (h21642 : p1339 ∨ p1330 ∨ p1333)
    (h21643 : (¬ p1339) ∨ (¬ p1338) ∨ p1333 ∨ p1330 ∨ (¬ p1336) ∨ (¬ p1337)) : p1330 ∨ p1333 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1330) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1333) := fun hu => hn (Or.inr hu)
  have u2 : p1336 := by
    rcases h21639 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1337 := by
    rcases h21640 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1338 := by
    rcases h21641 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1339 := by
    rcases h21642 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21643 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21645 (p1140 p1159 p1171 p1172 p1173 p1174 p1175 p1179 : Prop)
    (h6997 : p1171 ∨ p1179)
    (h7002 : p1172 ∨ p1179)
    (h7007 : p1173 ∨ p1179)
    (h7012 : p1174 ∨ p1179)
    (h7017 : p1175 ∨ p1179)
    (h6906 : p1140 ∨ p1159 ∨ (¬ p1171) ∨ (¬ p1172) ∨ (¬ p1173) ∨ (¬ p1174) ∨ (¬ p1175)) : p1179 ∨ p1159 ∨ p1140 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1179) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1159) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h6906 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21646 (p1140 p1159 p1171 p1176 p1177 p1178 p1179 p1180 : Prop)
    (h21645 : p1179 ∨ p1159 ∨ p1140)
    (h6994 : p1171 ∨ p1176)
    (h6995 : p1171 ∨ p1177)
    (h6996 : p1171 ∨ p1178)
    (h6998 : p1171 ∨ p1180)
    (h6931 : p1140 ∨ p1159 ∨ (¬ p1176) ∨ (¬ p1177) ∨ (¬ p1178) ∨ (¬ p1179) ∨ (¬ p1180)) : p1171 ∨ p1159 ∨ p1140 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1171) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1159) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1179 := by
    rcases h21645 with q0 | q1 | q2
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
  rcases h6931 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step21647 (p1140 p1159 p1172 p1176 p1177 p1178 p1179 p1180 : Prop)
    (h21645 : p1179 ∨ p1159 ∨ p1140)
    (h6999 : p1172 ∨ p1176)
    (h7000 : p1172 ∨ p1177)
    (h7001 : p1172 ∨ p1178)
    (h7003 : p1172 ∨ p1180)
    (h6931 : p1140 ∨ p1159 ∨ (¬ p1176) ∨ (¬ p1177) ∨ (¬ p1178) ∨ (¬ p1179) ∨ (¬ p1180)) : p1172 ∨ p1159 ∨ p1140 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1172) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1159) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1179 := by
    rcases h21645 with q0 | q1 | q2
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
  rcases h6931 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step21648 (p1140 p1159 p1173 p1176 p1177 p1178 p1179 p1180 : Prop)
    (h21645 : p1179 ∨ p1159 ∨ p1140)
    (h7004 : p1173 ∨ p1176)
    (h7005 : p1173 ∨ p1177)
    (h7006 : p1173 ∨ p1178)
    (h7008 : p1173 ∨ p1180)
    (h6931 : p1140 ∨ p1159 ∨ (¬ p1176) ∨ (¬ p1177) ∨ (¬ p1178) ∨ (¬ p1179) ∨ (¬ p1180)) : p1173 ∨ p1159 ∨ p1140 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1173) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1159) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1179 := by
    rcases h21645 with q0 | q1 | q2
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
  rcases h6931 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step21649 (p1140 p1159 p1174 p1176 p1177 p1178 p1179 p1180 : Prop)
    (h21645 : p1179 ∨ p1159 ∨ p1140)
    (h7009 : p1174 ∨ p1176)
    (h7010 : p1174 ∨ p1177)
    (h7011 : p1174 ∨ p1178)
    (h7013 : p1174 ∨ p1180)
    (h6931 : p1140 ∨ p1159 ∨ (¬ p1176) ∨ (¬ p1177) ∨ (¬ p1178) ∨ (¬ p1179) ∨ (¬ p1180)) : p1174 ∨ p1159 ∨ p1140 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1174) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1159) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1179 := by
    rcases h21645 with q0 | q1 | q2
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
  rcases h6931 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step21650 (p1140 p1159 p1171 p1172 p1173 p1174 p1175 p1176 p1177 p1178 p1179 p1180 : Prop)
    (h21645 : p1179 ∨ p1159 ∨ p1140)
    (h21646 : p1171 ∨ p1159 ∨ p1140)
    (h21647 : p1172 ∨ p1159 ∨ p1140)
    (h21648 : p1173 ∨ p1159 ∨ p1140)
    (h21649 : p1174 ∨ p1159 ∨ p1140)
    (h6906 : p1140 ∨ p1159 ∨ (¬ p1171) ∨ (¬ p1172) ∨ (¬ p1173) ∨ (¬ p1174) ∨ (¬ p1175))
    (h7014 : p1175 ∨ p1176)
    (h7015 : p1175 ∨ p1177)
    (h7016 : p1175 ∨ p1178)
    (h7018 : p1175 ∨ p1180)
    (h6931 : p1140 ∨ p1159 ∨ (¬ p1176) ∨ (¬ p1177) ∨ (¬ p1178) ∨ (¬ p1179) ∨ (¬ p1180)) : p1159 ∨ p1140 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1159) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1140) := fun hu => hn (Or.inr hu)
  have u2 : p1179 := by
    rcases h21645 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1171 := by
    rcases h21646 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1172 := by
    rcases h21647 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1173 := by
    rcases h21648 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p1174 := by
    rcases h21649 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p1175) := by
    rcases h6906 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p1176 := by
    rcases h7014 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p1177 := by
    rcases h7015 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p1178 := by
    rcases h7016 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p1180 := by
    rcases h7018 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h6931 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u11)

theorem step21651 (p1325 p1333 p1340 p1341 p1342 p1343 p1344 p1345 : Prop)
    (h8092 : p1340 ∨ p1341)
    (h8093 : p1340 ∨ p1342)
    (h8094 : p1340 ∨ p1343)
    (h8095 : p1340 ∨ p1344)
    (h8096 : p1340 ∨ p1345)
    (h8009 : p1325 ∨ p1333 ∨ (¬ p1341) ∨ (¬ p1342) ∨ (¬ p1343) ∨ (¬ p1344) ∨ (¬ p1345)) : p1340 ∨ p1325 ∨ p1333 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1340) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1333) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1341 := by
    rcases h8092 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1342 := by
    rcases h8093 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1343 := by
    rcases h8094 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1344 := by
    rcases h8095 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1345 := by
    rcases h8096 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8009 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21652 (p1325 p1333 p1336 p1341 p1342 p1343 p1344 p1345 : Prop)
    (h8072 : p1336 ∨ p1341)
    (h8073 : p1336 ∨ p1342)
    (h8074 : p1336 ∨ p1343)
    (h8075 : p1336 ∨ p1344)
    (h8076 : p1336 ∨ p1345)
    (h8009 : p1325 ∨ p1333 ∨ (¬ p1341) ∨ (¬ p1342) ∨ (¬ p1343) ∨ (¬ p1344) ∨ (¬ p1345)) : p1336 ∨ p1325 ∨ p1333 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1336) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1333) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1341 := by
    rcases h8072 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1342 := by
    rcases h8073 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1343 := by
    rcases h8074 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1344 := by
    rcases h8075 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1345 := by
    rcases h8076 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8009 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21653 (p1325 p1333 p1337 p1341 p1342 p1343 p1344 p1345 : Prop)
    (h8077 : p1337 ∨ p1341)
    (h8078 : p1337 ∨ p1342)
    (h8079 : p1337 ∨ p1343)
    (h8080 : p1337 ∨ p1344)
    (h8081 : p1337 ∨ p1345)
    (h8009 : p1325 ∨ p1333 ∨ (¬ p1341) ∨ (¬ p1342) ∨ (¬ p1343) ∨ (¬ p1344) ∨ (¬ p1345)) : p1337 ∨ p1325 ∨ p1333 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1337) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1333) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1341 := by
    rcases h8077 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1342 := by
    rcases h8078 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1343 := by
    rcases h8079 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1344 := by
    rcases h8080 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1345 := by
    rcases h8081 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8009 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21654 (p1325 p1333 p1338 p1341 p1342 p1343 p1344 p1345 : Prop)
    (h8082 : p1338 ∨ p1341)
    (h8083 : p1338 ∨ p1342)
    (h8084 : p1338 ∨ p1343)
    (h8085 : p1338 ∨ p1344)
    (h8086 : p1338 ∨ p1345)
    (h8009 : p1325 ∨ p1333 ∨ (¬ p1341) ∨ (¬ p1342) ∨ (¬ p1343) ∨ (¬ p1344) ∨ (¬ p1345)) : p1338 ∨ p1325 ∨ p1333 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1338) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1333) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h8009 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21655 (p1325 p1333 p1336 p1337 p1338 p1339 p1340 p1341 p1342 p1343 p1344 p1345 : Prop)
    (h7984 : p1325 ∨ p1333 ∨ (¬ p1336) ∨ (¬ p1337) ∨ (¬ p1338) ∨ (¬ p1339) ∨ (¬ p1340))
    (h8087 : p1339 ∨ p1341)
    (h8088 : p1339 ∨ p1342)
    (h8089 : p1339 ∨ p1343)
    (h8090 : p1339 ∨ p1344)
    (h8091 : p1339 ∨ p1345)
    (h8009 : p1325 ∨ p1333 ∨ (¬ p1341) ∨ (¬ p1342) ∨ (¬ p1343) ∨ (¬ p1344) ∨ (¬ p1345)) : (¬ p1338) ∨ (¬ p1340) ∨ p1333 ∨ p1325 ∨ (¬ p1336) ∨ (¬ p1337) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1338 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1340 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1333) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1336 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1337 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1339) := by
    rcases h7984 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u0)
    · exact q5
    · exact False.elim (q6 u1)
  have u7 : p1341 := by
    rcases h8087 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1342 := by
    rcases h8088 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1343 := by
    rcases h8089 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1344 := by
    rcases h8090 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1345 := by
    rcases h8091 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h8009 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21656 (p1325 p1333 p1336 p1337 p1338 p1340 : Prop)
    (h21651 : p1340 ∨ p1325 ∨ p1333)
    (h21652 : p1336 ∨ p1325 ∨ p1333)
    (h21653 : p1337 ∨ p1325 ∨ p1333)
    (h21654 : p1338 ∨ p1325 ∨ p1333)
    (h21655 : (¬ p1338) ∨ (¬ p1340) ∨ p1333 ∨ p1325 ∨ (¬ p1336) ∨ (¬ p1337)) : p1325 ∨ p1333 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1325) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1333) := fun hu => hn (Or.inr hu)
  have u2 : p1340 := by
    rcases h21651 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1336 := by
    rcases h21652 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1337 := by
    rcases h21653 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1338 := by
    rcases h21654 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21655 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step21658 (p187 p194 p196 p201 p202 p203 p204 p205 : Prop)
    (h1022 : p196 ∨ p201)
    (h1023 : p196 ∨ p202)
    (h1024 : p196 ∨ p203)
    (h1025 : p196 ∨ p204)
    (h1026 : p196 ∨ p205)
    (h955 : p187 ∨ p194 ∨ (¬ p201) ∨ (¬ p202) ∨ (¬ p203) ∨ (¬ p204) ∨ (¬ p205)) : p196 ∨ p187 ∨ p194 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p196) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p187) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p194) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p201 := by
    rcases h1022 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p202 := by
    rcases h1023 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p203 := by
    rcases h1024 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p204 := by
    rcases h1025 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p205 := by
    rcases h1026 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h955 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21659 (p187 p194 p197 p201 p202 p203 p204 p205 : Prop)
    (h1027 : p197 ∨ p201)
    (h1028 : p197 ∨ p202)
    (h1029 : p197 ∨ p203)
    (h1030 : p197 ∨ p204)
    (h1031 : p197 ∨ p205)
    (h955 : p187 ∨ p194 ∨ (¬ p201) ∨ (¬ p202) ∨ (¬ p203) ∨ (¬ p204) ∨ (¬ p205)) : p197 ∨ p187 ∨ p194 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p197) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p187) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p194) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p201 := by
    rcases h1027 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p202 := by
    rcases h1028 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p203 := by
    rcases h1029 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p204 := by
    rcases h1030 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p205 := by
    rcases h1031 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h955 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21660 (p187 p194 p198 p201 p202 p203 p204 p205 : Prop)
    (h1032 : p198 ∨ p201)
    (h1033 : p198 ∨ p202)
    (h1034 : p198 ∨ p203)
    (h1035 : p198 ∨ p204)
    (h1036 : p198 ∨ p205)
    (h955 : p187 ∨ p194 ∨ (¬ p201) ∨ (¬ p202) ∨ (¬ p203) ∨ (¬ p204) ∨ (¬ p205)) : p198 ∨ p187 ∨ p194 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p198) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p187) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p194) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p201 := by
    rcases h1032 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p202 := by
    rcases h1033 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p203 := by
    rcases h1034 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p204 := by
    rcases h1035 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p205 := by
    rcases h1036 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h955 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21661 (p187 p194 p199 p201 p202 p203 p204 p205 : Prop)
    (h1037 : p199 ∨ p201)
    (h1038 : p199 ∨ p202)
    (h1039 : p199 ∨ p203)
    (h1040 : p199 ∨ p204)
    (h1041 : p199 ∨ p205)
    (h955 : p187 ∨ p194 ∨ (¬ p201) ∨ (¬ p202) ∨ (¬ p203) ∨ (¬ p204) ∨ (¬ p205)) : p199 ∨ p187 ∨ p194 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p199) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p187) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p194) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p201 := by
    rcases h1037 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p202 := by
    rcases h1038 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p203 := by
    rcases h1039 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p204 := by
    rcases h1040 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p205 := by
    rcases h1041 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h955 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21662 (p187 p194 p196 p197 p198 p199 p200 p201 p202 p203 p204 p205 : Prop)
    (h930 : p187 ∨ p194 ∨ (¬ p196) ∨ (¬ p197) ∨ (¬ p198) ∨ (¬ p199) ∨ (¬ p200))
    (h1042 : p200 ∨ p201)
    (h1043 : p200 ∨ p202)
    (h1044 : p200 ∨ p203)
    (h1045 : p200 ∨ p204)
    (h1046 : p200 ∨ p205)
    (h955 : p187 ∨ p194 ∨ (¬ p201) ∨ (¬ p202) ∨ (¬ p203) ∨ (¬ p204) ∨ (¬ p205)) : (¬ p199) ∨ (¬ p198) ∨ p187 ∨ p194 ∨ (¬ p196) ∨ (¬ p197) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p199 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p198 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p187) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p194) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p196 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p197 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p200) := by
    rcases h930 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p201 := by
    rcases h1042 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p202 := by
    rcases h1043 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p203 := by
    rcases h1044 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p204 := by
    rcases h1045 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p205 := by
    rcases h1046 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h955 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21663 (p187 p194 p196 p197 p198 p199 : Prop)
    (h21658 : p196 ∨ p187 ∨ p194)
    (h21659 : p197 ∨ p187 ∨ p194)
    (h21660 : p198 ∨ p187 ∨ p194)
    (h21661 : p199 ∨ p187 ∨ p194)
    (h21662 : (¬ p199) ∨ (¬ p198) ∨ p187 ∨ p194 ∨ (¬ p196) ∨ (¬ p197)) : p187 ∨ p194 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p187) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p194) := fun hu => hn (Or.inr hu)
  have u2 : p196 := by
    rcases h21658 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p197 := by
    rcases h21659 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p198 := by
    rcases h21660 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p199 := by
    rcases h21661 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21662 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21664 (p301 p519 p522 p527 p528 p529 p530 p531 : Prop)
    (h2959 : p522 ∨ p527)
    (h2960 : p522 ∨ p528)
    (h2961 : p522 ∨ p529)
    (h2962 : p522 ∨ p530)
    (h2895 : p301 ∨ p519 ∨ (¬ p527) ∨ (¬ p528) ∨ (¬ p529) ∨ (¬ p530) ∨ (¬ p531)) : p522 ∨ (¬ p531) ∨ p519 ∨ p301 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p522) := fun hu => hn (Or.inl hu)
  have u1 : p531 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p519) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p301) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p527 := by
    rcases h2959 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p528 := by
    rcases h2960 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p529 := by
    rcases h2961 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p530 := by
    rcases h2962 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2895 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21665 (p301 p519 p523 p527 p528 p529 p530 p531 : Prop)
    (h2964 : p523 ∨ p527)
    (h2965 : p523 ∨ p528)
    (h2966 : p523 ∨ p529)
    (h2967 : p523 ∨ p530)
    (h2895 : p301 ∨ p519 ∨ (¬ p527) ∨ (¬ p528) ∨ (¬ p529) ∨ (¬ p530) ∨ (¬ p531)) : p523 ∨ (¬ p531) ∨ p519 ∨ p301 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p523) := fun hu => hn (Or.inl hu)
  have u1 : p531 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p519) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p301) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p527 := by
    rcases h2964 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p528 := by
    rcases h2965 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p529 := by
    rcases h2966 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p530 := by
    rcases h2967 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2895 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21667 (p344 p345 p346 p350 p352 p353 p354 p355 p356 p361 : Prop)
    (h21358 : p345 ∨ p344)
    (h7033 : (¬ p344) ∨ (¬ p346))
    (h21453 : (¬ p361) ∨ p350 ∨ p345)
    (h1929 : p352 ∨ p361)
    (h1934 : p353 ∨ p361)
    (h1939 : p354 ∨ p361)
    (h1944 : p355 ∨ p361)
    (h1949 : p356 ∨ p361)
    (h1838 : p346 ∨ p350 ∨ (¬ p352) ∨ (¬ p353) ∨ (¬ p354) ∨ (¬ p355) ∨ (¬ p356)) : p350 ∨ p345 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p350) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p345) := fun hu => hn (Or.inr hu)
  have u2 : p344 := by
    rcases h21358 with q0 | q1
    · exact False.elim (u1 q0)
    · exact q1
  have u3 : (¬ p346) := by
    rcases h7033 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u4 : (¬ p361) := by
    rcases h21453 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p352 := by
    rcases h1929 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u6 : p353 := by
    rcases h1934 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u7 : p354 := by
    rcases h1939 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u8 : p355 := by
    rcases h1944 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p356 := by
    rcases h1949 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h1838 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u9)

theorem step21668 (p258 p288 p291 p292 p293 p294 p295 p299 : Prop)
    (h21412 : (¬ p299) ∨ p258 ∨ p288)
    (h1549 : p291 ∨ p299)
    (h1554 : p292 ∨ p299)
    (h1559 : p293 ∨ p299)
    (h1564 : p294 ∨ p299)
    (h1569 : p295 ∨ p299)
    (h1458 : p258 ∨ p288 ∨ (¬ p291) ∨ (¬ p292) ∨ (¬ p293) ∨ (¬ p294) ∨ (¬ p295)) : p258 ∨ p288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p258) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p288) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p299) := by
    rcases h21412 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p291 := by
    rcases h1549 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : p292 := by
    rcases h1554 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p293 := by
    rcases h1559 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p294 := by
    rcases h1564 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p295 := by
    rcases h1569 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h1458 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21669 (p121 p1207 p1211 p1215 p1216 p1217 p1218 p1219 p1220 p1221 p1222 p1223 p1224 : Prop)
    (h21625 : p1215 ∨ (¬ p1223) ∨ p1211 ∨ p1207)
    (h21626 : p1216 ∨ (¬ p1223) ∨ p1211 ∨ p1207)
    (h21627 : p1217 ∨ (¬ p1223) ∨ p1211 ∨ p1207)
    (h21628 : p1218 ∨ (¬ p1223) ∨ p1211 ∨ p1207)
    (h7200 : p121 ∨ p1207 ∨ (¬ p1215) ∨ (¬ p1216) ∨ (¬ p1217) ∨ (¬ p1218) ∨ (¬ p1219))
    (h7318 : p1219 ∨ p1220)
    (h7319 : p1219 ∨ p1221)
    (h7320 : p1219 ∨ p1222)
    (h7322 : p1219 ∨ p1224)
    (h7225 : p121 ∨ p1207 ∨ (¬ p1220) ∨ (¬ p1221) ∨ (¬ p1222) ∨ (¬ p1223) ∨ (¬ p1224)) : (¬ p1223) ∨ p1211 ∨ p1207 ∨ p121 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1223 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1211) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1207) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p121) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1215 := by
    rcases h21625 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u5 : p1216 := by
    rcases h21626 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u6 : p1217 := by
    rcases h21627 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u7 : p1218 := by
    rcases h21628 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u8 : (¬ p1219) := by
    rcases h7200 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u6)
    · exact False.elim (q5 u7)
    · exact q6
  have u9 : p1220 := by
    rcases h7318 with q0 | q1
    · exact False.elim (u8 q0)
    · exact q1
  have u10 : p1221 := by
    rcases h7319 with q0 | q1
    · exact False.elim (u8 q0)
    · exact q1
  have u11 : p1222 := by
    rcases h7320 with q0 | q1
    · exact False.elim (u8 q0)
    · exact q1
  have u12 : p1224 := by
    rcases h7322 with q0 | q1
    · exact False.elim (u8 q0)
    · exact q1
  rcases h7225 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u12)

theorem step21670 (p121 p1207 p1211 p1215 p1216 p1217 p1218 p1219 p1223 : Prop)
    (h21669 : (¬ p1223) ∨ p1211 ∨ p1207 ∨ p121)
    (h7301 : p1215 ∨ p1223)
    (h7306 : p1216 ∨ p1223)
    (h7311 : p1217 ∨ p1223)
    (h7316 : p1218 ∨ p1223)
    (h7321 : p1219 ∨ p1223)
    (h7200 : p121 ∨ p1207 ∨ (¬ p1215) ∨ (¬ p1216) ∨ (¬ p1217) ∨ (¬ p1218) ∨ (¬ p1219)) : p1211 ∨ p1207 ∨ p121 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1211) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1207) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p121) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1223) := by
    rcases h21669 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u4 : p1215 := by
    rcases h7301 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u5 : p1216 := by
    rcases h7306 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p1217 := by
    rcases h7311 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p1218 := by
    rcases h7316 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p1219 := by
    rcases h7321 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h7200 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u8)

theorem step21672 (p167 p169 p173 p174 p175 p176 p177 p178 p179 p180 p181 p182 : Prop)
    (h825 : p167 ∨ p169 ∨ (¬ p178) ∨ (¬ p179) ∨ (¬ p180) ∨ (¬ p181) ∨ (¬ p182))
    (h893 : p173 ∨ p181)
    (h898 : p174 ∨ p181)
    (h903 : p175 ∨ p181)
    (h908 : p176 ∨ p181)
    (h913 : p177 ∨ p181)
    (h800 : p167 ∨ p169 ∨ (¬ p173) ∨ (¬ p174) ∨ (¬ p175) ∨ (¬ p176) ∨ (¬ p177)) : (¬ p179) ∨ (¬ p180) ∨ p167 ∨ p169 ∨ (¬ p178) ∨ (¬ p182) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p179 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p180 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p167) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p169) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p178 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p182 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p181) := by
    rcases h825 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u1)
    · exact q5
    · exact False.elim (q6 u5)
  have u7 : p173 := by
    rcases h893 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p174 := by
    rcases h898 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p175 := by
    rcases h903 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p176 := by
    rcases h908 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p177 := by
    rcases h913 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h800 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21673 (p3 p163 p165 p167 p169 p178 p179 p180 p182 p188 p193 p237 : Prop)
    (h21431 : (¬ p237) ∨ (¬ p188) ∨ p163 ∨ p3 ∨ p193)
    (h12250 : p3 ∨ (¬ p169) ∨ (¬ p188) ∨ (¬ p237))
    (h10851 : (¬ p163) ∨ (¬ p167))
    (h21427 : p182 ∨ p165 ∨ p169)
    (h21428 : p178 ∨ p165 ∨ p169)
    (h21429 : p179 ∨ p165 ∨ p169)
    (h21430 : p180 ∨ p165 ∨ p169)
    (h21672 : (¬ p179) ∨ (¬ p180) ∨ p167 ∨ p169 ∨ (¬ p178) ∨ (¬ p182)) : p3 ∨ (¬ p188) ∨ p165 ∨ (¬ p237) ∨ p193 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p165) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p193) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p163 := by
    rcases h21431 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u3)
    · exact False.elim (q1 u1)
    · exact q2
    · exact False.elim (u0 q3)
    · exact False.elim (u4 q4)
  have u6 : (¬ p169) := by
    rcases h12250 with q0 | q1 | q2 | q3
    · exact False.elim (u0 q0)
    · exact q1
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u3)
  have u7 : (¬ p167) := by
    rcases h10851 with q0 | q1
    · exact False.elim (q0 u5)
    · exact q1
  have u8 : p182 := by
    rcases h21427 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u2 q1)
    · exact False.elim (u6 q2)
  have u9 : p178 := by
    rcases h21428 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u2 q1)
    · exact False.elim (u6 q2)
  have u10 : p179 := by
    rcases h21429 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u2 q1)
    · exact False.elim (u6 q2)
  have u11 : p180 := by
    rcases h21430 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u2 q1)
    · exact False.elim (u6 q2)
  rcases h21672 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u11)
  · exact False.elim (u7 q2)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u8)

theorem step21674 (p163 p165 p167 p169 p173 p174 p175 p176 p177 p178 p179 p180 p181 p182 : Prop)
    (h21672 : (¬ p179) ∨ (¬ p180) ∨ p167 ∨ p169 ∨ (¬ p178) ∨ (¬ p182))
    (h10851 : (¬ p163) ∨ (¬ p167))
    (h817 : p163 ∨ p165 ∨ (¬ p178) ∨ (¬ p179) ∨ (¬ p180) ∨ (¬ p181) ∨ (¬ p182))
    (h893 : p173 ∨ p181)
    (h898 : p174 ∨ p181)
    (h903 : p175 ∨ p181)
    (h908 : p176 ∨ p181)
    (h913 : p177 ∨ p181)
    (h790 : p165 ∨ p169 ∨ (¬ p173) ∨ (¬ p174) ∨ (¬ p175) ∨ (¬ p176) ∨ (¬ p177)) : p165 ∨ p169 ∨ (¬ p182) ∨ (¬ p178) ∨ (¬ p179) ∨ (¬ p180) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p165) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p169) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p182 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p178 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p179 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p180 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p167 := by
    rcases h21672 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u4)
    · exact False.elim (q1 u5)
    · exact q2
    · exact False.elim (u1 q3)
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u2)
  have u7 : (¬ p163) := by
    rcases h10851 with q0 | q1
    · exact q0
    · exact False.elim (q1 u6)
  have u8 : (¬ p181) := by
    rcases h817 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u7 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact q5
    · exact False.elim (q6 u2)
  have u9 : p173 := by
    rcases h893 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u10 : p174 := by
    rcases h898 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u11 : p175 := by
    rcases h903 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u12 : p176 := by
    rcases h908 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u13 : p177 := by
    rcases h913 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h790 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u12)
  · exact False.elim (q6 u13)

theorem step21675 (p126 p516 p522 p527 p528 p529 p530 p531 : Prop)
    (h2959 : p522 ∨ p527)
    (h2960 : p522 ∨ p528)
    (h2961 : p522 ∨ p529)
    (h2962 : p522 ∨ p530)
    (h2963 : p522 ∨ p531)
    (h2901 : p126 ∨ p516 ∨ (¬ p527) ∨ (¬ p528) ∨ (¬ p529) ∨ (¬ p530) ∨ (¬ p531)) : p522 ∨ p516 ∨ p126 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p522) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p516) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p126) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p527 := by
    rcases h2959 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p528 := by
    rcases h2960 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p529 := by
    rcases h2961 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p530 := by
    rcases h2962 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p531 := by
    rcases h2963 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2901 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21676 (p126 p516 p523 p527 p528 p529 p530 p531 : Prop)
    (h2964 : p523 ∨ p527)
    (h2965 : p523 ∨ p528)
    (h2966 : p523 ∨ p529)
    (h2967 : p523 ∨ p530)
    (h2968 : p523 ∨ p531)
    (h2901 : p126 ∨ p516 ∨ (¬ p527) ∨ (¬ p528) ∨ (¬ p529) ∨ (¬ p530) ∨ (¬ p531)) : p523 ∨ p516 ∨ p126 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p523) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p516) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p126) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p527 := by
    rcases h2964 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p528 := by
    rcases h2965 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p529 := by
    rcases h2966 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p530 := by
    rcases h2967 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p531 := by
    rcases h2968 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2901 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21677 (p126 p516 p524 p527 p528 p529 p530 p531 : Prop)
    (h2969 : p524 ∨ p527)
    (h2970 : p524 ∨ p528)
    (h2971 : p524 ∨ p529)
    (h2972 : p524 ∨ p530)
    (h2973 : p524 ∨ p531)
    (h2901 : p126 ∨ p516 ∨ (¬ p527) ∨ (¬ p528) ∨ (¬ p529) ∨ (¬ p530) ∨ (¬ p531)) : p524 ∨ p516 ∨ p126 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p524) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p516) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p126) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p527 := by
    rcases h2969 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p528 := by
    rcases h2970 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p529 := by
    rcases h2971 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p530 := by
    rcases h2972 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p531 := by
    rcases h2973 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2901 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21678 (p126 p516 p525 p527 p528 p529 p530 p531 : Prop)
    (h2974 : p525 ∨ p527)
    (h2975 : p525 ∨ p528)
    (h2976 : p525 ∨ p529)
    (h2977 : p525 ∨ p530)
    (h2978 : p525 ∨ p531)
    (h2901 : p126 ∨ p516 ∨ (¬ p527) ∨ (¬ p528) ∨ (¬ p529) ∨ (¬ p530) ∨ (¬ p531)) : p525 ∨ p516 ∨ p126 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p525) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p516) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p126) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p527 := by
    rcases h2974 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p528 := by
    rcases h2975 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p529 := by
    rcases h2976 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p530 := by
    rcases h2977 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p531 := by
    rcases h2978 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2901 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21679 (p126 p516 p522 p523 p524 p525 p526 p527 p528 p529 p530 p531 : Prop)
    (h2876 : p126 ∨ p516 ∨ (¬ p522) ∨ (¬ p523) ∨ (¬ p524) ∨ (¬ p525) ∨ (¬ p526))
    (h2979 : p526 ∨ p527)
    (h2980 : p526 ∨ p528)
    (h2981 : p526 ∨ p529)
    (h2982 : p526 ∨ p530)
    (h2983 : p526 ∨ p531)
    (h2901 : p126 ∨ p516 ∨ (¬ p527) ∨ (¬ p528) ∨ (¬ p529) ∨ (¬ p530) ∨ (¬ p531)) : (¬ p525) ∨ (¬ p522) ∨ (¬ p523) ∨ p516 ∨ p126 ∨ (¬ p524) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p525 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p522 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p523 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p516) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p126) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p524 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p526) := by
    rcases h2876 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u4 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u2)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p527 := by
    rcases h2979 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p528 := by
    rcases h2980 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p529 := by
    rcases h2981 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p530 := by
    rcases h2982 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p531 := by
    rcases h2983 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h2901 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21680 (p126 p516 p522 p523 p524 p525 : Prop)
    (h21675 : p522 ∨ p516 ∨ p126)
    (h21676 : p523 ∨ p516 ∨ p126)
    (h21677 : p524 ∨ p516 ∨ p126)
    (h21678 : p525 ∨ p516 ∨ p126)
    (h21679 : (¬ p525) ∨ (¬ p522) ∨ (¬ p523) ∨ p516 ∨ p126 ∨ (¬ p524)) : p516 ∨ p126 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p516) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr hu)
  have u2 : p522 := by
    rcases h21675 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p523 := by
    rcases h21676 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p524 := by
    rcases h21677 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p525 := by
    rcases h21678 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21679 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (u0 q3)
  · exact False.elim (u1 q4)
  · exact False.elim (q5 u4)

theorem step21681 (p10 p323 p332 p333 p334 p335 p336 p337 p338 p339 p340 p341 : Prop)
    (h21596 : p341 ∨ p10 ∨ p323)
    (h21597 : p332 ∨ p10 ∨ p323)
    (h21598 : p333 ∨ p10 ∨ p323)
    (h21599 : p334 ∨ p10 ∨ p323)
    (h21600 : p335 ∨ p10 ∨ p323)
    (h1711 : p10 ∨ p323 ∨ (¬ p332) ∨ (¬ p333) ∨ (¬ p334) ∨ (¬ p335) ∨ (¬ p336))
    (h1819 : p336 ∨ p337)
    (h1820 : p336 ∨ p338)
    (h1821 : p336 ∨ p339)
    (h1822 : p336 ∨ p340)
    (h1736 : p10 ∨ p323 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341)) : p323 ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p323) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p10) := fun hu => hn (Or.inr hu)
  have u2 : p341 := by
    rcases h21596 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u3 : p332 := by
    rcases h21597 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u4 : p333 := by
    rcases h21598 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u5 : p334 := by
    rcases h21599 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u6 : p335 := by
    rcases h21600 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u7 : (¬ p336) := by
    rcases h1711 with q0 | q1 | q2 | q3 | q4 | q5 | q6
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
  have u11 : p340 := by
    rcases h1822 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h1736 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u2)

theorem step21683 (p576 p581 p588 p589 p590 p591 p592 p593 : Prop)
    (h3358 : p588 ∨ p589)
    (h3359 : p588 ∨ p590)
    (h3360 : p588 ∨ p591)
    (h3361 : p588 ∨ p592)
    (h3362 : p588 ∨ p593)
    (h3275 : p576 ∨ p581 ∨ (¬ p589) ∨ (¬ p590) ∨ (¬ p591) ∨ (¬ p592) ∨ (¬ p593)) : p588 ∨ p576 ∨ p581 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p588) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p581) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p589 := by
    rcases h3358 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p590 := by
    rcases h3359 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p591 := by
    rcases h3360 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p592 := by
    rcases h3361 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p593 := by
    rcases h3362 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3275 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21684 (p576 p581 p584 p589 p590 p591 p592 p593 : Prop)
    (h3338 : p584 ∨ p589)
    (h3339 : p584 ∨ p590)
    (h3340 : p584 ∨ p591)
    (h3341 : p584 ∨ p592)
    (h3342 : p584 ∨ p593)
    (h3275 : p576 ∨ p581 ∨ (¬ p589) ∨ (¬ p590) ∨ (¬ p591) ∨ (¬ p592) ∨ (¬ p593)) : p584 ∨ p576 ∨ p581 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p584) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p581) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p589 := by
    rcases h3338 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p590 := by
    rcases h3339 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p591 := by
    rcases h3340 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p592 := by
    rcases h3341 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p593 := by
    rcases h3342 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3275 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21685 (p576 p581 p585 p589 p590 p591 p592 p593 : Prop)
    (h3343 : p585 ∨ p589)
    (h3344 : p585 ∨ p590)
    (h3345 : p585 ∨ p591)
    (h3346 : p585 ∨ p592)
    (h3347 : p585 ∨ p593)
    (h3275 : p576 ∨ p581 ∨ (¬ p589) ∨ (¬ p590) ∨ (¬ p591) ∨ (¬ p592) ∨ (¬ p593)) : p585 ∨ p576 ∨ p581 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p585) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p581) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p589 := by
    rcases h3343 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p590 := by
    rcases h3344 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p591 := by
    rcases h3345 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p592 := by
    rcases h3346 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p593 := by
    rcases h3347 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3275 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21686 (p576 p581 p586 p589 p590 p591 p592 p593 : Prop)
    (h3348 : p586 ∨ p589)
    (h3349 : p586 ∨ p590)
    (h3350 : p586 ∨ p591)
    (h3351 : p586 ∨ p592)
    (h3352 : p586 ∨ p593)
    (h3275 : p576 ∨ p581 ∨ (¬ p589) ∨ (¬ p590) ∨ (¬ p591) ∨ (¬ p592) ∨ (¬ p593)) : p586 ∨ p576 ∨ p581 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p586) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p581) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h3275 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21687 (p576 p581 p584 p585 p586 p587 p588 p589 p590 p591 p592 p593 : Prop)
    (h3250 : p576 ∨ p581 ∨ (¬ p584) ∨ (¬ p585) ∨ (¬ p586) ∨ (¬ p587) ∨ (¬ p588))
    (h3353 : p587 ∨ p589)
    (h3354 : p587 ∨ p590)
    (h3355 : p587 ∨ p591)
    (h3356 : p587 ∨ p592)
    (h3357 : p587 ∨ p593)
    (h3275 : p576 ∨ p581 ∨ (¬ p589) ∨ (¬ p590) ∨ (¬ p591) ∨ (¬ p592) ∨ (¬ p593)) : (¬ p586) ∨ (¬ p584) ∨ p576 ∨ p581 ∨ (¬ p585) ∨ (¬ p588) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p586 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p581) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p585 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p588 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p587) := by
    rcases h3250 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u0)
    · exact q5
    · exact False.elim (q6 u5)
  have u7 : p589 := by
    rcases h3353 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p590 := by
    rcases h3354 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p591 := by
    rcases h3355 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p592 := by
    rcases h3356 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p593 := by
    rcases h3357 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h3275 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21688 (p576 p581 p584 p585 p586 p588 : Prop)
    (h21683 : p588 ∨ p576 ∨ p581)
    (h21684 : p584 ∨ p576 ∨ p581)
    (h21685 : p585 ∨ p576 ∨ p581)
    (h21686 : p586 ∨ p576 ∨ p581)
    (h21687 : (¬ p586) ∨ (¬ p584) ∨ p576 ∨ p581 ∨ (¬ p585) ∨ (¬ p588)) : p576 ∨ p581 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p576) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p581) := fun hu => hn (Or.inr hu)
  have u2 : p588 := by
    rcases h21683 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p584 := by
    rcases h21684 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p585 := by
    rcases h21685 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p586 := by
    rcases h21686 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21687 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u2)

theorem step21689 (p858 p862 p865 p866 p867 p868 p869 p871 : Prop)
    (h5028 : p865 ∨ p871)
    (h5033 : p866 ∨ p871)
    (h5038 : p867 ∨ p871)
    (h5043 : p868 ∨ p871)
    (h5048 : p869 ∨ p871)
    (h4938 : p858 ∨ p862 ∨ (¬ p865) ∨ (¬ p866) ∨ (¬ p867) ∨ (¬ p868) ∨ (¬ p869)) : p871 ∨ p858 ∨ p862 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p871) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p858) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p862) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p865 := by
    rcases h5028 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p866 := by
    rcases h5033 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p867 := by
    rcases h5038 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p868 := by
    rcases h5043 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p869 := by
    rcases h5048 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4938 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21690 (p858 p862 p865 p866 p867 p868 p869 p872 : Prop)
    (h5029 : p865 ∨ p872)
    (h5034 : p866 ∨ p872)
    (h5039 : p867 ∨ p872)
    (h5044 : p868 ∨ p872)
    (h5049 : p869 ∨ p872)
    (h4938 : p858 ∨ p862 ∨ (¬ p865) ∨ (¬ p866) ∨ (¬ p867) ∨ (¬ p868) ∨ (¬ p869)) : p872 ∨ p858 ∨ p862 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p872) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p858) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p862) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p865 := by
    rcases h5029 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p866 := by
    rcases h5034 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p867 := by
    rcases h5039 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p868 := by
    rcases h5044 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p869 := by
    rcases h5049 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4938 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21691 (p858 p862 p865 p866 p867 p868 p869 p873 : Prop)
    (h5030 : p865 ∨ p873)
    (h5035 : p866 ∨ p873)
    (h5040 : p867 ∨ p873)
    (h5045 : p868 ∨ p873)
    (h5050 : p869 ∨ p873)
    (h4938 : p858 ∨ p862 ∨ (¬ p865) ∨ (¬ p866) ∨ (¬ p867) ∨ (¬ p868) ∨ (¬ p869)) : p873 ∨ p858 ∨ p862 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p873) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p858) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p862) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p865 := by
    rcases h5030 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p866 := by
    rcases h5035 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p867 := by
    rcases h5040 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p868 := by
    rcases h5045 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p869 := by
    rcases h5050 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4938 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21692 (p858 p862 p865 p866 p867 p868 p869 p874 : Prop)
    (h5031 : p865 ∨ p874)
    (h5036 : p866 ∨ p874)
    (h5041 : p867 ∨ p874)
    (h5046 : p868 ∨ p874)
    (h5051 : p869 ∨ p874)
    (h4938 : p858 ∨ p862 ∨ (¬ p865) ∨ (¬ p866) ∨ (¬ p867) ∨ (¬ p868) ∨ (¬ p869)) : p874 ∨ p858 ∨ p862 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p874) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p858) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p862) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p865 := by
    rcases h5031 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p866 := by
    rcases h5036 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p867 := by
    rcases h5041 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p868 := by
    rcases h5046 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p869 := by
    rcases h5051 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4938 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21693 (p858 p862 p865 p866 p867 p868 p869 p870 p871 p872 p873 p874 : Prop)
    (h4963 : p858 ∨ p862 ∨ (¬ p870) ∨ (¬ p871) ∨ (¬ p872) ∨ (¬ p873) ∨ (¬ p874))
    (h5027 : p865 ∨ p870)
    (h5032 : p866 ∨ p870)
    (h5037 : p867 ∨ p870)
    (h5042 : p868 ∨ p870)
    (h5047 : p869 ∨ p870)
    (h4938 : p858 ∨ p862 ∨ (¬ p865) ∨ (¬ p866) ∨ (¬ p867) ∨ (¬ p868) ∨ (¬ p869)) : (¬ p874) ∨ (¬ p872) ∨ p858 ∨ p862 ∨ (¬ p873) ∨ (¬ p871) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p874 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p872 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p858) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p862) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p873 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p871 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p870) := by
    rcases h4963 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact q2
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u0)
  have u7 : p865 := by
    rcases h5027 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p866 := by
    rcases h5032 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p867 := by
    rcases h5037 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p868 := by
    rcases h5042 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p869 := by
    rcases h5047 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h4938 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21694 (p858 p862 p871 p872 p873 p874 : Prop)
    (h21689 : p871 ∨ p858 ∨ p862)
    (h21690 : p872 ∨ p858 ∨ p862)
    (h21691 : p873 ∨ p858 ∨ p862)
    (h21692 : p874 ∨ p858 ∨ p862)
    (h21693 : (¬ p874) ∨ (¬ p872) ∨ p858 ∨ p862 ∨ (¬ p873) ∨ (¬ p871)) : p858 ∨ p862 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p858) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p862) := fun hu => hn (Or.inr hu)
  have u2 : p871 := by
    rcases h21689 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p872 := by
    rcases h21690 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p873 := by
    rcases h21691 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p874 := by
    rcases h21692 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21693 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u2)

theorem step21695 (p17 p268 p269 p270 p271 p272 p273 p276 : Prop)
    (h1415 : p269 ∨ p276)
    (h1420 : p270 ∨ p276)
    (h1425 : p271 ∨ p276)
    (h1430 : p272 ∨ p276)
    (h1435 : p273 ∨ p276)
    (h1327 : p17 ∨ p268 ∨ (¬ p269) ∨ (¬ p270) ∨ (¬ p271) ∨ (¬ p272) ∨ (¬ p273)) : p276 ∨ p268 ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p276) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p268) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p269 := by
    rcases h1415 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p270 := by
    rcases h1420 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p271 := by
    rcases h1425 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p272 := by
    rcases h1430 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p273 := by
    rcases h1435 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1327 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21696 (p17 p268 p269 p270 p271 p272 p273 p277 : Prop)
    (h1416 : p269 ∨ p277)
    (h1421 : p270 ∨ p277)
    (h1426 : p271 ∨ p277)
    (h1431 : p272 ∨ p277)
    (h1436 : p273 ∨ p277)
    (h1327 : p17 ∨ p268 ∨ (¬ p269) ∨ (¬ p270) ∨ (¬ p271) ∨ (¬ p272) ∨ (¬ p273)) : p277 ∨ p268 ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p277) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p268) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p269 := by
    rcases h1416 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p270 := by
    rcases h1421 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p271 := by
    rcases h1426 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p272 := by
    rcases h1431 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p273 := by
    rcases h1436 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1327 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21697 (p17 p268 p269 p270 p271 p272 p273 p278 : Prop)
    (h1417 : p269 ∨ p278)
    (h1422 : p270 ∨ p278)
    (h1427 : p271 ∨ p278)
    (h1432 : p272 ∨ p278)
    (h1437 : p273 ∨ p278)
    (h1327 : p17 ∨ p268 ∨ (¬ p269) ∨ (¬ p270) ∨ (¬ p271) ∨ (¬ p272) ∨ (¬ p273)) : p278 ∨ p268 ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p278) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p268) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p269 := by
    rcases h1417 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p270 := by
    rcases h1422 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p271 := by
    rcases h1427 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p272 := by
    rcases h1432 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p273 := by
    rcases h1437 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1327 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21698 (p17 p268 p269 p270 p271 p272 p273 p274 : Prop)
    (h1413 : p269 ∨ p274)
    (h1418 : p270 ∨ p274)
    (h1423 : p271 ∨ p274)
    (h1428 : p272 ∨ p274)
    (h1433 : p273 ∨ p274)
    (h1327 : p17 ∨ p268 ∨ (¬ p269) ∨ (¬ p270) ∨ (¬ p271) ∨ (¬ p272) ∨ (¬ p273)) : p274 ∨ p268 ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p274) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p268) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p269 := by
    rcases h1413 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p270 := by
    rcases h1418 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p271 := by
    rcases h1423 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p272 := by
    rcases h1428 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p273 := by
    rcases h1433 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1327 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21700 (p303 p386 p394 p395 p396 p397 p398 p399 : Prop)
    (h2201 : p394 ∨ p395)
    (h2202 : p394 ∨ p396)
    (h2203 : p394 ∨ p397)
    (h2205 : p394 ∨ p399)
    (h2117 : p303 ∨ p386 ∨ (¬ p395) ∨ (¬ p396) ∨ (¬ p397) ∨ (¬ p398) ∨ (¬ p399)) : p394 ∨ (¬ p398) ∨ p303 ∨ p386 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p394) := fun hu => hn (Or.inl hu)
  have u1 : p398 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p386) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p395 := by
    rcases h2201 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p396 := by
    rcases h2202 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p397 := by
    rcases h2203 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p399 := by
    rcases h2205 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2117 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step21703 (p303 p386 p390 p391 p392 p393 p394 p398 : Prop)
    (h2184 : p390 ∨ p398)
    (h2189 : p391 ∨ p398)
    (h2194 : p392 ∨ p398)
    (h2199 : p393 ∨ p398)
    (h2204 : p394 ∨ p398)
    (h2092 : p303 ∨ p386 ∨ (¬ p390) ∨ (¬ p391) ∨ (¬ p392) ∨ (¬ p393) ∨ (¬ p394)) : p398 ∨ p303 ∨ p386 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p398) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p386) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h2092 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21704 (p303 p386 p390 p395 p396 p397 p398 p399 : Prop)
    (h21703 : p398 ∨ p303 ∨ p386)
    (h2181 : p390 ∨ p395)
    (h2182 : p390 ∨ p396)
    (h2183 : p390 ∨ p397)
    (h2185 : p390 ∨ p399)
    (h2117 : p303 ∨ p386 ∨ (¬ p395) ∨ (¬ p396) ∨ (¬ p397) ∨ (¬ p398) ∨ (¬ p399)) : p390 ∨ p303 ∨ p386 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p390) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p386) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p398 := by
    rcases h21703 with q0 | q1 | q2
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
  rcases h2117 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step21705 (p303 p386 p391 p395 p396 p397 p398 p399 : Prop)
    (h21703 : p398 ∨ p303 ∨ p386)
    (h2186 : p391 ∨ p395)
    (h2187 : p391 ∨ p396)
    (h2188 : p391 ∨ p397)
    (h2190 : p391 ∨ p399)
    (h2117 : p303 ∨ p386 ∨ (¬ p395) ∨ (¬ p396) ∨ (¬ p397) ∨ (¬ p398) ∨ (¬ p399)) : p391 ∨ p303 ∨ p386 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p391) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p386) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p398 := by
    rcases h21703 with q0 | q1 | q2
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
  rcases h2117 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step21706 (p303 p386 p392 p395 p396 p397 p398 p399 : Prop)
    (h21703 : p398 ∨ p303 ∨ p386)
    (h2191 : p392 ∨ p395)
    (h2192 : p392 ∨ p396)
    (h2193 : p392 ∨ p397)
    (h2195 : p392 ∨ p399)
    (h2117 : p303 ∨ p386 ∨ (¬ p395) ∨ (¬ p396) ∨ (¬ p397) ∨ (¬ p398) ∨ (¬ p399)) : p392 ∨ p303 ∨ p386 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p392) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p386) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p398 := by
    rcases h21703 with q0 | q1 | q2
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
  rcases h2117 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step21707 (p303 p386 p390 p391 p392 p393 p394 p395 p396 p397 p398 p399 : Prop)
    (h21700 : p394 ∨ (¬ p398) ∨ p303 ∨ p386)
    (h21704 : p390 ∨ p303 ∨ p386)
    (h21705 : p391 ∨ p303 ∨ p386)
    (h21706 : p392 ∨ p303 ∨ p386)
    (h2092 : p303 ∨ p386 ∨ (¬ p390) ∨ (¬ p391) ∨ (¬ p392) ∨ (¬ p393) ∨ (¬ p394))
    (h2196 : p393 ∨ p395)
    (h2197 : p393 ∨ p396)
    (h2198 : p393 ∨ p397)
    (h2200 : p393 ∨ p399)
    (h2117 : p303 ∨ p386 ∨ (¬ p395) ∨ (¬ p396) ∨ (¬ p397) ∨ (¬ p398) ∨ (¬ p399)) : (¬ p398) ∨ p303 ∨ p386 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p398 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p386) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p394 := by
    rcases h21700 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u4 : p390 := by
    rcases h21704 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u5 : p391 := by
    rcases h21705 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u6 : p392 := by
    rcases h21706 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u7 : (¬ p393) := by
    rcases h2092 with q0 | q1 | q2 | q3 | q4 | q5 | q6
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
  rcases h2117 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u11)

theorem step21708 (p303 p386 p398 : Prop)
    (h21703 : p398 ∨ p303 ∨ p386)
    (h21707 : (¬ p398) ∨ p303 ∨ p386) : p303 ∨ p386 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p386) := fun hu => hn (Or.inr hu)
  have u2 : p398 := by
    rcases h21703 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21707 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)

theorem step21710 (p595 p614 p623 p628 p629 p630 p631 p632 : Prop)
    (h3590 : p623 ∨ p628)
    (h3591 : p623 ∨ p629)
    (h3592 : p623 ∨ p630)
    (h3593 : p623 ∨ p631)
    (h3594 : p623 ∨ p632)
    (h3517 : p595 ∨ p614 ∨ (¬ p628) ∨ (¬ p629) ∨ (¬ p630) ∨ (¬ p631) ∨ (¬ p632)) : p623 ∨ p614 ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p623) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p614) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p628 := by
    rcases h3590 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p629 := by
    rcases h3591 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p630 := by
    rcases h3592 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p631 := by
    rcases h3593 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p632 := by
    rcases h3594 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3517 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21711 (p595 p614 p624 p628 p629 p630 p631 p632 : Prop)
    (h3595 : p624 ∨ p628)
    (h3596 : p624 ∨ p629)
    (h3597 : p624 ∨ p630)
    (h3598 : p624 ∨ p631)
    (h3599 : p624 ∨ p632)
    (h3517 : p595 ∨ p614 ∨ (¬ p628) ∨ (¬ p629) ∨ (¬ p630) ∨ (¬ p631) ∨ (¬ p632)) : p624 ∨ p614 ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p624) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p614) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p628 := by
    rcases h3595 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p629 := by
    rcases h3596 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p630 := by
    rcases h3597 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p631 := by
    rcases h3598 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p632 := by
    rcases h3599 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3517 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21712 (p595 p614 p625 p628 p629 p630 p631 p632 : Prop)
    (h3600 : p625 ∨ p628)
    (h3601 : p625 ∨ p629)
    (h3602 : p625 ∨ p630)
    (h3603 : p625 ∨ p631)
    (h3604 : p625 ∨ p632)
    (h3517 : p595 ∨ p614 ∨ (¬ p628) ∨ (¬ p629) ∨ (¬ p630) ∨ (¬ p631) ∨ (¬ p632)) : p625 ∨ p614 ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p625) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p614) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p628 := by
    rcases h3600 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p629 := by
    rcases h3601 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p630 := by
    rcases h3602 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p631 := by
    rcases h3603 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p632 := by
    rcases h3604 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3517 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21713 (p595 p614 p626 p628 p629 p630 p631 p632 : Prop)
    (h3605 : p626 ∨ p628)
    (h3606 : p626 ∨ p629)
    (h3607 : p626 ∨ p630)
    (h3608 : p626 ∨ p631)
    (h3609 : p626 ∨ p632)
    (h3517 : p595 ∨ p614 ∨ (¬ p628) ∨ (¬ p629) ∨ (¬ p630) ∨ (¬ p631) ∨ (¬ p632)) : p626 ∨ p614 ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p626) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p614) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p628 := by
    rcases h3605 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p629 := by
    rcases h3606 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p630 := by
    rcases h3607 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p631 := by
    rcases h3608 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p632 := by
    rcases h3609 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3517 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21714 (p595 p614 p623 p624 p625 p626 p627 p628 p629 p630 p631 p632 : Prop)
    (h3492 : p595 ∨ p614 ∨ (¬ p623) ∨ (¬ p624) ∨ (¬ p625) ∨ (¬ p626) ∨ (¬ p627))
    (h3610 : p627 ∨ p628)
    (h3611 : p627 ∨ p629)
    (h3612 : p627 ∨ p630)
    (h3613 : p627 ∨ p631)
    (h3614 : p627 ∨ p632)
    (h3517 : p595 ∨ p614 ∨ (¬ p628) ∨ (¬ p629) ∨ (¬ p630) ∨ (¬ p631) ∨ (¬ p632)) : (¬ p626) ∨ (¬ p625) ∨ p595 ∨ p614 ∨ (¬ p623) ∨ (¬ p624) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p626 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p625 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p614) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p623 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p624 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p627) := by
    rcases h3492 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p628 := by
    rcases h3610 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p629 := by
    rcases h3611 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p630 := by
    rcases h3612 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p631 := by
    rcases h3613 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p632 := by
    rcases h3614 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h3517 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21715 (p595 p614 p623 p624 p625 p626 : Prop)
    (h21710 : p623 ∨ p614 ∨ p595)
    (h21711 : p624 ∨ p614 ∨ p595)
    (h21712 : p625 ∨ p614 ∨ p595)
    (h21713 : p626 ∨ p614 ∨ p595)
    (h21714 : (¬ p626) ∨ (¬ p625) ∨ p595 ∨ p614 ∨ (¬ p623) ∨ (¬ p624)) : p614 ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p614) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p595) := fun hu => hn (Or.inr hu)
  have u2 : p623 := by
    rcases h21710 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p624 := by
    rcases h21711 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p625 := by
    rcases h21712 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p626 := by
    rcases h21713 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21714 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21716 (p657 p662 p674 p675 p676 p677 p678 p679 : Prop)
    (h3879 : p674 ∨ p675)
    (h3880 : p674 ∨ p676)
    (h3881 : p674 ∨ p677)
    (h3882 : p674 ∨ p678)
    (h3786 : p657 ∨ p662 ∨ (¬ p675) ∨ (¬ p676) ∨ (¬ p677) ∨ (¬ p678) ∨ (¬ p679)) : p674 ∨ (¬ p679) ∨ p662 ∨ p657 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p674) := fun hu => hn (Or.inl hu)
  have u1 : p679 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p662) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p657) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h3786 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21717 (p657 p662 p670 p671 p672 p673 p674 p675 : Prop)
    (h3859 : p670 ∨ p675)
    (h3864 : p671 ∨ p675)
    (h3869 : p672 ∨ p675)
    (h3874 : p673 ∨ p675)
    (h3761 : p657 ∨ p662 ∨ (¬ p670) ∨ (¬ p671) ∨ (¬ p672) ∨ (¬ p673) ∨ (¬ p674)) : p675 ∨ (¬ p674) ∨ p662 ∨ p657 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p675) := fun hu => hn (Or.inl hu)
  have u1 : p674 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p662) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p657) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h3761 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21718 (p657 p662 p670 p671 p672 p673 p674 p676 : Prop)
    (h3860 : p670 ∨ p676)
    (h3865 : p671 ∨ p676)
    (h3870 : p672 ∨ p676)
    (h3875 : p673 ∨ p676)
    (h3761 : p657 ∨ p662 ∨ (¬ p670) ∨ (¬ p671) ∨ (¬ p672) ∨ (¬ p673) ∨ (¬ p674)) : p676 ∨ (¬ p674) ∨ p662 ∨ p657 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p676) := fun hu => hn (Or.inl hu)
  have u1 : p674 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p662) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p657) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h3761 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21719 (p657 p662 p670 p671 p672 p673 p674 p677 : Prop)
    (h3861 : p670 ∨ p677)
    (h3866 : p671 ∨ p677)
    (h3871 : p672 ∨ p677)
    (h3876 : p673 ∨ p677)
    (h3761 : p657 ∨ p662 ∨ (¬ p670) ∨ (¬ p671) ∨ (¬ p672) ∨ (¬ p673) ∨ (¬ p674)) : p677 ∨ (¬ p674) ∨ p662 ∨ p657 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p677) := fun hu => hn (Or.inl hu)
  have u1 : p674 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p662) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p657) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h3761 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21720 (p657 p662 p670 p671 p672 p673 p674 p675 p676 p677 p678 p679 : Prop)
    (h21716 : p674 ∨ (¬ p679) ∨ p662 ∨ p657)
    (h21717 : p675 ∨ (¬ p674) ∨ p662 ∨ p657)
    (h21718 : p676 ∨ (¬ p674) ∨ p662 ∨ p657)
    (h21719 : p677 ∨ (¬ p674) ∨ p662 ∨ p657)
    (h3786 : p657 ∨ p662 ∨ (¬ p675) ∨ (¬ p676) ∨ (¬ p677) ∨ (¬ p678) ∨ (¬ p679))
    (h3862 : p670 ∨ p678)
    (h3867 : p671 ∨ p678)
    (h3872 : p672 ∨ p678)
    (h3877 : p673 ∨ p678)
    (h3761 : p657 ∨ p662 ∨ (¬ p670) ∨ (¬ p671) ∨ (¬ p672) ∨ (¬ p673) ∨ (¬ p674)) : (¬ p679) ∨ p662 ∨ p657 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p679 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p662) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p657) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p674 := by
    rcases h21716 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u4 : p675 := by
    rcases h21717 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u5 : p676 := by
    rcases h21718 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u6 : p677 := by
    rcases h21719 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u7 : (¬ p678) := by
    rcases h3786 with q0 | q1 | q2 | q3 | q4 | q5 | q6
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
  rcases h3761 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u3)

theorem step21721 (p657 p662 p670 p671 p672 p673 p674 p679 : Prop)
    (h21720 : (¬ p679) ∨ p662 ∨ p657)
    (h3863 : p670 ∨ p679)
    (h3868 : p671 ∨ p679)
    (h3873 : p672 ∨ p679)
    (h3878 : p673 ∨ p679)
    (h3883 : p674 ∨ p679)
    (h3761 : p657 ∨ p662 ∨ (¬ p670) ∨ (¬ p671) ∨ (¬ p672) ∨ (¬ p673) ∨ (¬ p674)) : p662 ∨ p657 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p662) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p657) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p679) := by
    rcases h21720 with q0 | q1 | q2
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
  rcases h3761 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21722 (p996 p997 p1005 p1006 p1007 p1008 p1009 p1014 : Prop)
    (h5942 : p1005 ∨ p1014)
    (h5947 : p1006 ∨ p1014)
    (h5952 : p1007 ∨ p1014)
    (h5957 : p1008 ∨ p1014)
    (h5962 : p1009 ∨ p1014)
    (h5840 : p996 ∨ p997 ∨ (¬ p1005) ∨ (¬ p1006) ∨ (¬ p1007) ∨ (¬ p1008) ∨ (¬ p1009)) : p1014 ∨ p997 ∨ p996 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1014) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p997) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p996) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1005 := by
    rcases h5942 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1006 := by
    rcases h5947 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1007 := by
    rcases h5952 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1008 := by
    rcases h5957 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1009 := by
    rcases h5962 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5840 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21723 (p996 p997 p1005 p1006 p1007 p1008 p1009 p1010 : Prop)
    (h5938 : p1005 ∨ p1010)
    (h5943 : p1006 ∨ p1010)
    (h5948 : p1007 ∨ p1010)
    (h5953 : p1008 ∨ p1010)
    (h5958 : p1009 ∨ p1010)
    (h5840 : p996 ∨ p997 ∨ (¬ p1005) ∨ (¬ p1006) ∨ (¬ p1007) ∨ (¬ p1008) ∨ (¬ p1009)) : p1010 ∨ p997 ∨ p996 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1010) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p997) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p996) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1005 := by
    rcases h5938 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1006 := by
    rcases h5943 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1007 := by
    rcases h5948 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1008 := by
    rcases h5953 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1009 := by
    rcases h5958 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5840 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21724 (p996 p997 p1005 p1006 p1007 p1008 p1009 p1011 : Prop)
    (h5939 : p1005 ∨ p1011)
    (h5944 : p1006 ∨ p1011)
    (h5949 : p1007 ∨ p1011)
    (h5954 : p1008 ∨ p1011)
    (h5959 : p1009 ∨ p1011)
    (h5840 : p996 ∨ p997 ∨ (¬ p1005) ∨ (¬ p1006) ∨ (¬ p1007) ∨ (¬ p1008) ∨ (¬ p1009)) : p1011 ∨ p997 ∨ p996 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1011) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p997) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p996) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1005 := by
    rcases h5939 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1006 := by
    rcases h5944 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1007 := by
    rcases h5949 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1008 := by
    rcases h5954 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1009 := by
    rcases h5959 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5840 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21725 (p996 p997 p1005 p1006 p1007 p1008 p1009 p1012 : Prop)
    (h5940 : p1005 ∨ p1012)
    (h5945 : p1006 ∨ p1012)
    (h5950 : p1007 ∨ p1012)
    (h5955 : p1008 ∨ p1012)
    (h5960 : p1009 ∨ p1012)
    (h5840 : p996 ∨ p997 ∨ (¬ p1005) ∨ (¬ p1006) ∨ (¬ p1007) ∨ (¬ p1008) ∨ (¬ p1009)) : p1012 ∨ p997 ∨ p996 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1012) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p997) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p996) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h5840 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21726 (p996 p997 p1005 p1006 p1007 p1008 p1009 p1010 p1011 p1012 p1013 p1014 : Prop)
    (h5865 : p996 ∨ p997 ∨ (¬ p1010) ∨ (¬ p1011) ∨ (¬ p1012) ∨ (¬ p1013) ∨ (¬ p1014))
    (h5941 : p1005 ∨ p1013)
    (h5946 : p1006 ∨ p1013)
    (h5951 : p1007 ∨ p1013)
    (h5956 : p1008 ∨ p1013)
    (h5961 : p1009 ∨ p1013)
    (h5840 : p996 ∨ p997 ∨ (¬ p1005) ∨ (¬ p1006) ∨ (¬ p1007) ∨ (¬ p1008) ∨ (¬ p1009)) : (¬ p1012) ∨ p997 ∨ p996 ∨ (¬ p1014) ∨ (¬ p1010) ∨ (¬ p1011) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1012 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p997) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p996) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1014 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1010 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1011 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1013) := by
    rcases h5865 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u0)
    · exact q5
    · exact False.elim (q6 u3)
  have u7 : p1005 := by
    rcases h5941 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1006 := by
    rcases h5946 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1007 := by
    rcases h5951 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1008 := by
    rcases h5956 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1009 := by
    rcases h5961 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h5840 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21727 (p996 p997 p1010 p1011 p1012 p1014 : Prop)
    (h21722 : p1014 ∨ p997 ∨ p996)
    (h21723 : p1010 ∨ p997 ∨ p996)
    (h21724 : p1011 ∨ p997 ∨ p996)
    (h21725 : p1012 ∨ p997 ∨ p996)
    (h21726 : (¬ p1012) ∨ p997 ∨ p996 ∨ (¬ p1014) ∨ (¬ p1010) ∨ (¬ p1011)) : p997 ∨ p996 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p997) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p996) := fun hu => hn (Or.inr hu)
  have u2 : p1014 := by
    rcases h21722 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1010 := by
    rcases h21723 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1011 := by
    rcases h21724 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1012 := by
    rcases h21725 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21726 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step21728 (p1711 p1713 p1722 p1723 p1724 p1725 p1726 p1727 : Prop)
    (h10970 : p1722 ∨ p1727)
    (h10975 : p1723 ∨ p1727)
    (h10980 : p1724 ∨ p1727)
    (h10985 : p1725 ∨ p1727)
    (h10990 : p1726 ∨ p1727)
    (h10882 : p1711 ∨ p1713 ∨ (¬ p1722) ∨ (¬ p1723) ∨ (¬ p1724) ∨ (¬ p1725) ∨ (¬ p1726)) : p1727 ∨ p1713 ∨ p1711 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1727) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1713) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1711) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1722 := by
    rcases h10970 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1723 := by
    rcases h10975 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1724 := by
    rcases h10980 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1725 := by
    rcases h10985 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1726 := by
    rcases h10990 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h10882 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21729 (p1711 p1713 p1722 p1723 p1724 p1725 p1726 p1728 : Prop)
    (h10971 : p1722 ∨ p1728)
    (h10976 : p1723 ∨ p1728)
    (h10981 : p1724 ∨ p1728)
    (h10986 : p1725 ∨ p1728)
    (h10991 : p1726 ∨ p1728)
    (h10882 : p1711 ∨ p1713 ∨ (¬ p1722) ∨ (¬ p1723) ∨ (¬ p1724) ∨ (¬ p1725) ∨ (¬ p1726)) : p1728 ∨ p1713 ∨ p1711 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1728) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1713) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1711) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1722 := by
    rcases h10971 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1723 := by
    rcases h10976 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1724 := by
    rcases h10981 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1725 := by
    rcases h10986 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1726 := by
    rcases h10991 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h10882 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21730 (p1711 p1713 p1722 p1723 p1724 p1725 p1726 p1729 : Prop)
    (h10972 : p1722 ∨ p1729)
    (h10977 : p1723 ∨ p1729)
    (h10982 : p1724 ∨ p1729)
    (h10987 : p1725 ∨ p1729)
    (h10992 : p1726 ∨ p1729)
    (h10882 : p1711 ∨ p1713 ∨ (¬ p1722) ∨ (¬ p1723) ∨ (¬ p1724) ∨ (¬ p1725) ∨ (¬ p1726)) : p1729 ∨ p1713 ∨ p1711 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1729) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1713) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1711) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1722 := by
    rcases h10972 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1723 := by
    rcases h10977 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1724 := by
    rcases h10982 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1725 := by
    rcases h10987 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1726 := by
    rcases h10992 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h10882 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21731 (p1711 p1713 p1722 p1723 p1724 p1725 p1726 p1730 : Prop)
    (h10973 : p1722 ∨ p1730)
    (h10978 : p1723 ∨ p1730)
    (h10983 : p1724 ∨ p1730)
    (h10988 : p1725 ∨ p1730)
    (h10993 : p1726 ∨ p1730)
    (h10882 : p1711 ∨ p1713 ∨ (¬ p1722) ∨ (¬ p1723) ∨ (¬ p1724) ∨ (¬ p1725) ∨ (¬ p1726)) : p1730 ∨ p1713 ∨ p1711 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1730) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1713) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1711) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1722 := by
    rcases h10973 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1723 := by
    rcases h10978 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1724 := by
    rcases h10983 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1725 := by
    rcases h10988 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1726 := by
    rcases h10993 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h10882 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21732 (p1711 p1713 p1722 p1723 p1724 p1725 p1726 p1727 p1728 p1729 p1730 p1731 : Prop)
    (h10907 : p1711 ∨ p1713 ∨ (¬ p1727) ∨ (¬ p1728) ∨ (¬ p1729) ∨ (¬ p1730) ∨ (¬ p1731))
    (h10974 : p1722 ∨ p1731)
    (h10979 : p1723 ∨ p1731)
    (h10984 : p1724 ∨ p1731)
    (h10989 : p1725 ∨ p1731)
    (h10994 : p1726 ∨ p1731)
    (h10882 : p1711 ∨ p1713 ∨ (¬ p1722) ∨ (¬ p1723) ∨ (¬ p1724) ∨ (¬ p1725) ∨ (¬ p1726)) : (¬ p1730) ∨ (¬ p1729) ∨ p1711 ∨ p1713 ∨ (¬ p1727) ∨ (¬ p1728) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1730 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1729 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1711) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1713) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1727 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1731) := by
    rcases h10907 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p1722 := by
    rcases h10974 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1723 := by
    rcases h10979 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1724 := by
    rcases h10984 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1725 := by
    rcases h10989 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1726 := by
    rcases h10994 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h10882 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21733 (p1711 p1713 p1727 p1728 p1729 p1730 : Prop)
    (h21728 : p1727 ∨ p1713 ∨ p1711)
    (h21729 : p1728 ∨ p1713 ∨ p1711)
    (h21730 : p1729 ∨ p1713 ∨ p1711)
    (h21731 : p1730 ∨ p1713 ∨ p1711)
    (h21732 : (¬ p1730) ∨ (¬ p1729) ∨ p1711 ∨ p1713 ∨ (¬ p1727) ∨ (¬ p1728)) : p1713 ∨ p1711 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1713) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1711) := fun hu => hn (Or.inr hu)
  have u2 : p1727 := by
    rcases h21728 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1728 := by
    rcases h21729 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1729 := by
    rcases h21730 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1730 := by
    rcases h21731 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21732 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21734 (p1665 p1666 p1695 p1696 p1697 p1698 p1699 p1700 : Prop)
    (h10526 : p1695 ∨ p1700)
    (h10531 : p1696 ∨ p1700)
    (h10536 : p1697 ∨ p1700)
    (h10541 : p1698 ∨ p1700)
    (h10546 : p1699 ∨ p1700)
    (h10438 : p1665 ∨ p1666 ∨ (¬ p1695) ∨ (¬ p1696) ∨ (¬ p1697) ∨ (¬ p1698) ∨ (¬ p1699)) : p1700 ∨ p1665 ∨ p1666 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1700) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1665) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1666) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1695 := by
    rcases h10526 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1696 := by
    rcases h10531 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1697 := by
    rcases h10536 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1698 := by
    rcases h10541 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1699 := by
    rcases h10546 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h10438 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21735 (p1665 p1666 p1695 p1696 p1697 p1698 p1699 p1701 : Prop)
    (h10527 : p1695 ∨ p1701)
    (h10532 : p1696 ∨ p1701)
    (h10537 : p1697 ∨ p1701)
    (h10542 : p1698 ∨ p1701)
    (h10547 : p1699 ∨ p1701)
    (h10438 : p1665 ∨ p1666 ∨ (¬ p1695) ∨ (¬ p1696) ∨ (¬ p1697) ∨ (¬ p1698) ∨ (¬ p1699)) : p1701 ∨ p1665 ∨ p1666 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1701) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1665) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1666) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1695 := by
    rcases h10527 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1696 := by
    rcases h10532 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1697 := by
    rcases h10537 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1698 := by
    rcases h10542 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1699 := by
    rcases h10547 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h10438 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21736 (p1665 p1666 p1695 p1696 p1697 p1698 p1699 p1702 : Prop)
    (h10528 : p1695 ∨ p1702)
    (h10533 : p1696 ∨ p1702)
    (h10538 : p1697 ∨ p1702)
    (h10543 : p1698 ∨ p1702)
    (h10548 : p1699 ∨ p1702)
    (h10438 : p1665 ∨ p1666 ∨ (¬ p1695) ∨ (¬ p1696) ∨ (¬ p1697) ∨ (¬ p1698) ∨ (¬ p1699)) : p1702 ∨ p1665 ∨ p1666 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1702) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1665) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1666) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1695 := by
    rcases h10528 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1696 := by
    rcases h10533 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1697 := by
    rcases h10538 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1698 := by
    rcases h10543 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1699 := by
    rcases h10548 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h10438 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21737 (p1665 p1666 p1695 p1696 p1697 p1698 p1699 p1703 : Prop)
    (h10529 : p1695 ∨ p1703)
    (h10534 : p1696 ∨ p1703)
    (h10539 : p1697 ∨ p1703)
    (h10544 : p1698 ∨ p1703)
    (h10549 : p1699 ∨ p1703)
    (h10438 : p1665 ∨ p1666 ∨ (¬ p1695) ∨ (¬ p1696) ∨ (¬ p1697) ∨ (¬ p1698) ∨ (¬ p1699)) : p1703 ∨ p1665 ∨ p1666 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1703) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1665) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1666) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1695 := by
    rcases h10529 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1696 := by
    rcases h10534 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1697 := by
    rcases h10539 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1698 := by
    rcases h10544 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1699 := by
    rcases h10549 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h10438 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21738 (p1665 p1666 p1695 p1696 p1697 p1698 p1699 p1700 p1701 p1702 p1703 p1704 : Prop)
    (h10463 : p1665 ∨ p1666 ∨ (¬ p1700) ∨ (¬ p1701) ∨ (¬ p1702) ∨ (¬ p1703) ∨ (¬ p1704))
    (h10530 : p1695 ∨ p1704)
    (h10535 : p1696 ∨ p1704)
    (h10540 : p1697 ∨ p1704)
    (h10545 : p1698 ∨ p1704)
    (h10550 : p1699 ∨ p1704)
    (h10438 : p1665 ∨ p1666 ∨ (¬ p1695) ∨ (¬ p1696) ∨ (¬ p1697) ∨ (¬ p1698) ∨ (¬ p1699)) : (¬ p1703) ∨ (¬ p1702) ∨ p1666 ∨ p1665 ∨ (¬ p1700) ∨ (¬ p1701) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1703 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1702 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1666) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1665) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1700 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1701 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1704) := by
    rcases h10463 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p1695 := by
    rcases h10530 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1696 := by
    rcases h10535 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1697 := by
    rcases h10540 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1698 := by
    rcases h10545 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1699 := by
    rcases h10550 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h10438 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21739 (p1665 p1666 p1700 p1701 p1702 p1703 : Prop)
    (h21734 : p1700 ∨ p1665 ∨ p1666)
    (h21735 : p1701 ∨ p1665 ∨ p1666)
    (h21736 : p1702 ∨ p1665 ∨ p1666)
    (h21737 : p1703 ∨ p1665 ∨ p1666)
    (h21738 : (¬ p1703) ∨ (¬ p1702) ∨ p1666 ∨ p1665 ∨ (¬ p1700) ∨ (¬ p1701)) : p1665 ∨ p1666 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1665) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1666) := fun hu => hn (Or.inr hu)
  have u2 : p1700 := by
    rcases h21734 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1701 := by
    rcases h21735 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1702 := by
    rcases h21736 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1703 := by
    rcases h21737 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21738 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21740 (p726 p757 p759 p760 p761 p762 p763 p767 : Prop)
    (h4384 : p759 ∨ p767)
    (h4389 : p760 ∨ p767)
    (h4394 : p761 ∨ p767)
    (h4399 : p762 ∨ p767)
    (h4404 : p763 ∨ p767)
    (h4294 : p726 ∨ p757 ∨ (¬ p759) ∨ (¬ p760) ∨ (¬ p761) ∨ (¬ p762) ∨ (¬ p763)) : p767 ∨ p757 ∨ p726 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p767) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p757) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p726) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p759 := by
    rcases h4384 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p760 := by
    rcases h4389 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p761 := by
    rcases h4394 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p762 := by
    rcases h4399 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p763 := by
    rcases h4404 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4294 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21741 (p726 p757 p759 p760 p761 p762 p763 p768 : Prop)
    (h4385 : p759 ∨ p768)
    (h4390 : p760 ∨ p768)
    (h4395 : p761 ∨ p768)
    (h4400 : p762 ∨ p768)
    (h4405 : p763 ∨ p768)
    (h4294 : p726 ∨ p757 ∨ (¬ p759) ∨ (¬ p760) ∨ (¬ p761) ∨ (¬ p762) ∨ (¬ p763)) : p768 ∨ p757 ∨ p726 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p768) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p757) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p726) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p759 := by
    rcases h4385 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p760 := by
    rcases h4390 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p761 := by
    rcases h4395 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p762 := by
    rcases h4400 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p763 := by
    rcases h4405 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4294 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21742 (p726 p757 p759 p760 p761 p762 p763 p764 : Prop)
    (h4381 : p759 ∨ p764)
    (h4386 : p760 ∨ p764)
    (h4391 : p761 ∨ p764)
    (h4396 : p762 ∨ p764)
    (h4401 : p763 ∨ p764)
    (h4294 : p726 ∨ p757 ∨ (¬ p759) ∨ (¬ p760) ∨ (¬ p761) ∨ (¬ p762) ∨ (¬ p763)) : p764 ∨ p757 ∨ p726 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p764) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p757) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p726) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p759 := by
    rcases h4381 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p760 := by
    rcases h4386 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p761 := by
    rcases h4391 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p762 := by
    rcases h4396 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p763 := by
    rcases h4401 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4294 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21743 (p726 p757 p759 p760 p761 p762 p763 p765 : Prop)
    (h4382 : p759 ∨ p765)
    (h4387 : p760 ∨ p765)
    (h4392 : p761 ∨ p765)
    (h4397 : p762 ∨ p765)
    (h4402 : p763 ∨ p765)
    (h4294 : p726 ∨ p757 ∨ (¬ p759) ∨ (¬ p760) ∨ (¬ p761) ∨ (¬ p762) ∨ (¬ p763)) : p765 ∨ p757 ∨ p726 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p765) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p757) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p726) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p759 := by
    rcases h4382 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p760 := by
    rcases h4387 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p761 := by
    rcases h4392 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p762 := by
    rcases h4397 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p763 := by
    rcases h4402 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4294 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21745 (p726 p757 p759 p760 p761 p762 p763 p764 p765 p766 p767 p768 : Prop)
    (h4319 : p726 ∨ p757 ∨ (¬ p764) ∨ (¬ p765) ∨ (¬ p766) ∨ (¬ p767) ∨ (¬ p768))
    (h4383 : p759 ∨ p766)
    (h4388 : p760 ∨ p766)
    (h4393 : p761 ∨ p766)
    (h4398 : p762 ∨ p766)
    (h4403 : p763 ∨ p766)
    (h4294 : p726 ∨ p757 ∨ (¬ p759) ∨ (¬ p760) ∨ (¬ p761) ∨ (¬ p762) ∨ (¬ p763)) : (¬ p765) ∨ p757 ∨ p726 ∨ (¬ p767) ∨ (¬ p764) ∨ (¬ p768) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p765 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p757) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p726) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p767 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p764 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p768 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p766) := by
    rcases h4319 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u0)
    · exact q4
    · exact False.elim (q5 u3)
    · exact False.elim (q6 u5)
  have u7 : p759 := by
    rcases h4383 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p760 := by
    rcases h4388 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p761 := by
    rcases h4393 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p762 := by
    rcases h4398 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p763 := by
    rcases h4403 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h4294 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21746 (p726 p757 p764 p765 p767 p768 : Prop)
    (h21740 : p767 ∨ p757 ∨ p726)
    (h21741 : p768 ∨ p757 ∨ p726)
    (h21742 : p764 ∨ p757 ∨ p726)
    (h21743 : p765 ∨ p757 ∨ p726)
    (h21745 : (¬ p765) ∨ p757 ∨ p726 ∨ (¬ p767) ∨ (¬ p764) ∨ (¬ p768)) : p757 ∨ p726 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p757) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p726) := fun hu => hn (Or.inr hu)
  have u2 : p767 := by
    rcases h21740 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p768 := by
    rcases h21741 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p764 := by
    rcases h21742 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p765 := by
    rcases h21743 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21745 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step21747 (p382 p406 p409 p410 p411 p412 p413 p414 : Prop)
    (h2306 : p409 ∨ p414)
    (h2311 : p410 ∨ p414)
    (h2316 : p411 ∨ p414)
    (h2321 : p412 ∨ p414)
    (h2326 : p413 ∨ p414)
    (h2218 : p382 ∨ p406 ∨ (¬ p409) ∨ (¬ p410) ∨ (¬ p411) ∨ (¬ p412) ∨ (¬ p413)) : p414 ∨ p382 ∨ p406 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p414) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p406) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p409 := by
    rcases h2306 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p410 := by
    rcases h2311 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p411 := by
    rcases h2316 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p412 := by
    rcases h2321 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p413 := by
    rcases h2326 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2218 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21748 (p382 p406 p409 p410 p411 p412 p413 p415 : Prop)
    (h2307 : p409 ∨ p415)
    (h2312 : p410 ∨ p415)
    (h2317 : p411 ∨ p415)
    (h2322 : p412 ∨ p415)
    (h2327 : p413 ∨ p415)
    (h2218 : p382 ∨ p406 ∨ (¬ p409) ∨ (¬ p410) ∨ (¬ p411) ∨ (¬ p412) ∨ (¬ p413)) : p415 ∨ p382 ∨ p406 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p415) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p406) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p409 := by
    rcases h2307 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p410 := by
    rcases h2312 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p411 := by
    rcases h2317 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p412 := by
    rcases h2322 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p413 := by
    rcases h2327 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2218 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21749 (p382 p406 p409 p410 p411 p412 p413 p416 : Prop)
    (h2308 : p409 ∨ p416)
    (h2313 : p410 ∨ p416)
    (h2318 : p411 ∨ p416)
    (h2323 : p412 ∨ p416)
    (h2328 : p413 ∨ p416)
    (h2218 : p382 ∨ p406 ∨ (¬ p409) ∨ (¬ p410) ∨ (¬ p411) ∨ (¬ p412) ∨ (¬ p413)) : p416 ∨ p382 ∨ p406 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p416) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p406) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p409 := by
    rcases h2308 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p410 := by
    rcases h2313 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p411 := by
    rcases h2318 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p412 := by
    rcases h2323 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p413 := by
    rcases h2328 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2218 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21750 (p382 p406 p409 p410 p411 p412 p413 p417 : Prop)
    (h2309 : p409 ∨ p417)
    (h2314 : p410 ∨ p417)
    (h2319 : p411 ∨ p417)
    (h2324 : p412 ∨ p417)
    (h2329 : p413 ∨ p417)
    (h2218 : p382 ∨ p406 ∨ (¬ p409) ∨ (¬ p410) ∨ (¬ p411) ∨ (¬ p412) ∨ (¬ p413)) : p417 ∨ p382 ∨ p406 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p417) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h2218 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21751 (p382 p406 p409 p410 p411 p412 p413 p414 p415 p416 p417 p418 : Prop)
    (h2243 : p382 ∨ p406 ∨ (¬ p414) ∨ (¬ p415) ∨ (¬ p416) ∨ (¬ p417) ∨ (¬ p418))
    (h2310 : p409 ∨ p418)
    (h2315 : p410 ∨ p418)
    (h2320 : p411 ∨ p418)
    (h2325 : p412 ∨ p418)
    (h2330 : p413 ∨ p418)
    (h2218 : p382 ∨ p406 ∨ (¬ p409) ∨ (¬ p410) ∨ (¬ p411) ∨ (¬ p412) ∨ (¬ p413)) : (¬ p417) ∨ (¬ p416) ∨ p406 ∨ p382 ∨ (¬ p414) ∨ (¬ p415) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p417 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p416 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p406) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p414 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p415 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p418) := by
    rcases h2243 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p409 := by
    rcases h2310 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p410 := by
    rcases h2315 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p411 := by
    rcases h2320 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p412 := by
    rcases h2325 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p413 := by
    rcases h2330 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h2218 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21752 (p382 p406 p414 p415 p416 p417 : Prop)
    (h21747 : p414 ∨ p382 ∨ p406)
    (h21748 : p415 ∨ p382 ∨ p406)
    (h21749 : p416 ∨ p382 ∨ p406)
    (h21750 : p417 ∨ p382 ∨ p406)
    (h21751 : (¬ p417) ∨ (¬ p416) ∨ p406 ∨ p382 ∨ (¬ p414) ∨ (¬ p415)) : p382 ∨ p406 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p406) := fun hu => hn (Or.inr hu)
  have u2 : p414 := by
    rcases h21747 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p415 := by
    rcases h21748 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p416 := by
    rcases h21749 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p417 := by
    rcases h21750 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21751 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21753 (p127 p206 p214 p215 p216 p217 p218 p219 : Prop)
    (h1147 : p214 ∨ p219)
    (h1152 : p215 ∨ p219)
    (h1157 : p216 ∨ p219)
    (h1162 : p217 ∨ p219)
    (h1167 : p218 ∨ p219)
    (h1049 : p127 ∨ p206 ∨ (¬ p214) ∨ (¬ p215) ∨ (¬ p216) ∨ (¬ p217) ∨ (¬ p218)) : p219 ∨ p127 ∨ p206 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p219) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p127) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p206) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p214 := by
    rcases h1147 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p215 := by
    rcases h1152 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p216 := by
    rcases h1157 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p217 := by
    rcases h1162 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p218 := by
    rcases h1167 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1049 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21754 (p127 p206 p214 p215 p216 p217 p218 p220 : Prop)
    (h1148 : p214 ∨ p220)
    (h1153 : p215 ∨ p220)
    (h1158 : p216 ∨ p220)
    (h1163 : p217 ∨ p220)
    (h1168 : p218 ∨ p220)
    (h1049 : p127 ∨ p206 ∨ (¬ p214) ∨ (¬ p215) ∨ (¬ p216) ∨ (¬ p217) ∨ (¬ p218)) : p220 ∨ p127 ∨ p206 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p220) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p127) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p206) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p214 := by
    rcases h1148 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p215 := by
    rcases h1153 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p216 := by
    rcases h1158 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p217 := by
    rcases h1163 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p218 := by
    rcases h1168 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1049 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21755 (p127 p206 p214 p215 p216 p217 p218 p221 : Prop)
    (h1149 : p214 ∨ p221)
    (h1154 : p215 ∨ p221)
    (h1159 : p216 ∨ p221)
    (h1164 : p217 ∨ p221)
    (h1169 : p218 ∨ p221)
    (h1049 : p127 ∨ p206 ∨ (¬ p214) ∨ (¬ p215) ∨ (¬ p216) ∨ (¬ p217) ∨ (¬ p218)) : p221 ∨ p127 ∨ p206 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p221) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p127) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p206) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p214 := by
    rcases h1149 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p215 := by
    rcases h1154 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p216 := by
    rcases h1159 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p217 := by
    rcases h1164 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p218 := by
    rcases h1169 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1049 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21756 (p127 p206 p214 p215 p216 p217 p218 p222 : Prop)
    (h1150 : p214 ∨ p222)
    (h1155 : p215 ∨ p222)
    (h1160 : p216 ∨ p222)
    (h1165 : p217 ∨ p222)
    (h1170 : p218 ∨ p222)
    (h1049 : p127 ∨ p206 ∨ (¬ p214) ∨ (¬ p215) ∨ (¬ p216) ∨ (¬ p217) ∨ (¬ p218)) : p222 ∨ p127 ∨ p206 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p222) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p127) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p206) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h1049 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21758 (p104 p108 p115 p116 p117 p118 p119 p120 : Prop)
    (h640 : p115 ∨ p116)
    (h641 : p115 ∨ p117)
    (h642 : p115 ∨ p118)
    (h643 : p115 ∨ p119)
    (h644 : p115 ∨ p120)
    (h551 : p104 ∨ p108 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p115 ∨ p104 ∨ p108 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p115) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p104) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p108) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p116 := by
    rcases h640 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p117 := by
    rcases h641 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p118 := by
    rcases h642 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p119 := by
    rcases h643 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p120 := by
    rcases h644 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h551 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21759 (p104 p108 p111 p116 p117 p118 p119 p120 : Prop)
    (h620 : p111 ∨ p116)
    (h621 : p111 ∨ p117)
    (h622 : p111 ∨ p118)
    (h623 : p111 ∨ p119)
    (h624 : p111 ∨ p120)
    (h551 : p104 ∨ p108 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p111 ∨ p104 ∨ p108 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p111) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p104) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p108) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p116 := by
    rcases h620 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p117 := by
    rcases h621 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p118 := by
    rcases h622 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p119 := by
    rcases h623 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p120 := by
    rcases h624 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h551 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21760 (p104 p108 p112 p116 p117 p118 p119 p120 : Prop)
    (h625 : p112 ∨ p116)
    (h626 : p112 ∨ p117)
    (h627 : p112 ∨ p118)
    (h628 : p112 ∨ p119)
    (h629 : p112 ∨ p120)
    (h551 : p104 ∨ p108 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p112 ∨ p104 ∨ p108 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p112) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p104) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p108) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p116 := by
    rcases h625 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p117 := by
    rcases h626 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p118 := by
    rcases h627 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p119 := by
    rcases h628 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p120 := by
    rcases h629 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h551 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21761 (p104 p108 p113 p116 p117 p118 p119 p120 : Prop)
    (h630 : p113 ∨ p116)
    (h631 : p113 ∨ p117)
    (h632 : p113 ∨ p118)
    (h633 : p113 ∨ p119)
    (h634 : p113 ∨ p120)
    (h551 : p104 ∨ p108 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p113 ∨ p104 ∨ p108 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p113) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p104) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p108) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p116 := by
    rcases h630 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p117 := by
    rcases h631 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p118 := by
    rcases h632 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p119 := by
    rcases h633 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p120 := by
    rcases h634 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h551 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21763 (p127 p206 p214 p215 p216 p217 p218 p219 p220 p221 p222 p223 : Prop)
    (h1074 : p127 ∨ p206 ∨ (¬ p219) ∨ (¬ p220) ∨ (¬ p221) ∨ (¬ p222) ∨ (¬ p223))
    (h1151 : p214 ∨ p223)
    (h1156 : p215 ∨ p223)
    (h1161 : p216 ∨ p223)
    (h1166 : p217 ∨ p223)
    (h1171 : p218 ∨ p223)
    (h1049 : p127 ∨ p206 ∨ (¬ p214) ∨ (¬ p215) ∨ (¬ p216) ∨ (¬ p217) ∨ (¬ p218)) : (¬ p222) ∨ (¬ p221) ∨ p127 ∨ p206 ∨ (¬ p219) ∨ (¬ p220) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p222 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p221 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p127) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p206) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p219 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p220 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p223) := by
    rcases h1074 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p214 := by
    rcases h1151 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p215 := by
    rcases h1156 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p216 := by
    rcases h1161 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p217 := by
    rcases h1166 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p218 := by
    rcases h1171 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h1049 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21764 (p127 p206 p219 p220 p221 p222 : Prop)
    (h21753 : p219 ∨ p127 ∨ p206)
    (h21754 : p220 ∨ p127 ∨ p206)
    (h21755 : p221 ∨ p127 ∨ p206)
    (h21756 : p222 ∨ p127 ∨ p206)
    (h21763 : (¬ p222) ∨ (¬ p221) ∨ p127 ∨ p206 ∨ (¬ p219) ∨ (¬ p220)) : p127 ∨ p206 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p127) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p206) := fun hu => hn (Or.inr hu)
  have u2 : p219 := by
    rcases h21753 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p220 := by
    rcases h21754 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p221 := by
    rcases h21755 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p222 := by
    rcases h21756 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21763 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21773 (p68 p71 p73 p74 p75 p76 p77 p80 : Prop)
    (h371 : p73 ∨ p80)
    (h376 : p74 ∨ p80)
    (h381 : p75 ∨ p80)
    (h386 : p76 ∨ p80)
    (h391 : p77 ∨ p80)
    (h275 : p68 ∨ p71 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77)) : p80 ∨ p71 ∨ p68 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p80) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p71) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p68) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p73 := by
    rcases h371 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p74 := by
    rcases h376 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p75 := by
    rcases h381 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p76 := by
    rcases h386 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p77 := by
    rcases h391 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h275 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21774 (p68 p71 p73 p74 p75 p76 p77 p81 : Prop)
    (h372 : p73 ∨ p81)
    (h377 : p74 ∨ p81)
    (h382 : p75 ∨ p81)
    (h387 : p76 ∨ p81)
    (h392 : p77 ∨ p81)
    (h275 : p68 ∨ p71 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77)) : p81 ∨ p71 ∨ p68 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p81) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p71) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p68) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p73 := by
    rcases h372 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p74 := by
    rcases h377 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p75 := by
    rcases h382 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p76 := by
    rcases h387 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p77 := by
    rcases h392 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h275 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21775 (p68 p71 p73 p74 p75 p76 p77 p82 : Prop)
    (h373 : p73 ∨ p82)
    (h378 : p74 ∨ p82)
    (h383 : p75 ∨ p82)
    (h388 : p76 ∨ p82)
    (h393 : p77 ∨ p82)
    (h275 : p68 ∨ p71 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77)) : p82 ∨ p71 ∨ p68 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p82) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p71) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p68) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p73 := by
    rcases h373 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p74 := by
    rcases h378 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p75 := by
    rcases h383 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p76 := by
    rcases h388 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p77 := by
    rcases h393 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h275 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21776 (p68 p71 p73 p74 p75 p76 p77 p78 : Prop)
    (h369 : p73 ∨ p78)
    (h374 : p74 ∨ p78)
    (h379 : p75 ∨ p78)
    (h384 : p76 ∨ p78)
    (h389 : p77 ∨ p78)
    (h275 : p68 ∨ p71 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77)) : p78 ∨ p71 ∨ p68 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p78) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p71) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p68) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h275 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21777 (p68 p71 p73 p74 p75 p76 p77 p78 p79 p80 p81 p82 : Prop)
    (h300 : p68 ∨ p71 ∨ (¬ p78) ∨ (¬ p79) ∨ (¬ p80) ∨ (¬ p81) ∨ (¬ p82))
    (h370 : p73 ∨ p79)
    (h375 : p74 ∨ p79)
    (h380 : p75 ∨ p79)
    (h385 : p76 ∨ p79)
    (h390 : p77 ∨ p79)
    (h275 : p68 ∨ p71 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77)) : (¬ p78) ∨ p71 ∨ p68 ∨ (¬ p80) ∨ (¬ p82) ∨ (¬ p81) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p78 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p71) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p68) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p80 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p82 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p81 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p79) := by
    rcases h300 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u0)
    · exact q3
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u4)
  have u7 : p73 := by
    rcases h370 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p74 := by
    rcases h375 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p75 := by
    rcases h380 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p76 := by
    rcases h385 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p77 := by
    rcases h390 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h275 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21778 (p68 p71 p78 p80 p81 p82 : Prop)
    (h21773 : p80 ∨ p71 ∨ p68)
    (h21774 : p81 ∨ p71 ∨ p68)
    (h21775 : p82 ∨ p71 ∨ p68)
    (h21776 : p78 ∨ p71 ∨ p68)
    (h21777 : (¬ p78) ∨ p71 ∨ p68 ∨ (¬ p80) ∨ (¬ p82) ∨ (¬ p81)) : p71 ∨ p68 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p71) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p68) := fun hu => hn (Or.inr hu)
  have u2 : p80 := by
    rcases h21773 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p81 := by
    rcases h21774 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p82 := by
    rcases h21775 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p78 := by
    rcases h21776 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21777 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step21779 (p1189 p1193 p1200 p1201 p1202 p1203 p1204 p1205 : Prop)
    (h7183 : p1200 ∨ p1201)
    (h7184 : p1200 ∨ p1202)
    (h7185 : p1200 ∨ p1203)
    (h7186 : p1200 ∨ p1204)
    (h7187 : p1200 ∨ p1205)
    (h7094 : p1189 ∨ p1193 ∨ (¬ p1201) ∨ (¬ p1202) ∨ (¬ p1203) ∨ (¬ p1204) ∨ (¬ p1205)) : p1200 ∨ p1189 ∨ p1193 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1200) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1193) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1201 := by
    rcases h7183 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1202 := by
    rcases h7184 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1203 := by
    rcases h7185 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1204 := by
    rcases h7186 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1205 := by
    rcases h7187 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7094 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21780 (p1189 p1193 p1196 p1201 p1202 p1203 p1204 p1205 : Prop)
    (h7163 : p1196 ∨ p1201)
    (h7164 : p1196 ∨ p1202)
    (h7165 : p1196 ∨ p1203)
    (h7166 : p1196 ∨ p1204)
    (h7167 : p1196 ∨ p1205)
    (h7094 : p1189 ∨ p1193 ∨ (¬ p1201) ∨ (¬ p1202) ∨ (¬ p1203) ∨ (¬ p1204) ∨ (¬ p1205)) : p1196 ∨ p1189 ∨ p1193 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1196) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1193) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1201 := by
    rcases h7163 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1202 := by
    rcases h7164 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1203 := by
    rcases h7165 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1204 := by
    rcases h7166 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1205 := by
    rcases h7167 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7094 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21781 (p1189 p1193 p1197 p1201 p1202 p1203 p1204 p1205 : Prop)
    (h7168 : p1197 ∨ p1201)
    (h7169 : p1197 ∨ p1202)
    (h7170 : p1197 ∨ p1203)
    (h7171 : p1197 ∨ p1204)
    (h7172 : p1197 ∨ p1205)
    (h7094 : p1189 ∨ p1193 ∨ (¬ p1201) ∨ (¬ p1202) ∨ (¬ p1203) ∨ (¬ p1204) ∨ (¬ p1205)) : p1197 ∨ p1189 ∨ p1193 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1197) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1193) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h7094 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21782 (p1189 p1193 p1198 p1201 p1202 p1203 p1204 p1205 : Prop)
    (h7173 : p1198 ∨ p1201)
    (h7174 : p1198 ∨ p1202)
    (h7175 : p1198 ∨ p1203)
    (h7176 : p1198 ∨ p1204)
    (h7177 : p1198 ∨ p1205)
    (h7094 : p1189 ∨ p1193 ∨ (¬ p1201) ∨ (¬ p1202) ∨ (¬ p1203) ∨ (¬ p1204) ∨ (¬ p1205)) : p1198 ∨ p1189 ∨ p1193 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1198) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1193) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1201 := by
    rcases h7173 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1202 := by
    rcases h7174 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1203 := by
    rcases h7175 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1204 := by
    rcases h7176 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1205 := by
    rcases h7177 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7094 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21783 (p1189 p1193 p1196 p1197 p1198 p1199 p1200 p1201 p1202 p1203 p1204 p1205 : Prop)
    (h7069 : p1189 ∨ p1193 ∨ (¬ p1196) ∨ (¬ p1197) ∨ (¬ p1198) ∨ (¬ p1199) ∨ (¬ p1200))
    (h7178 : p1199 ∨ p1201)
    (h7179 : p1199 ∨ p1202)
    (h7180 : p1199 ∨ p1203)
    (h7181 : p1199 ∨ p1204)
    (h7182 : p1199 ∨ p1205)
    (h7094 : p1189 ∨ p1193 ∨ (¬ p1201) ∨ (¬ p1202) ∨ (¬ p1203) ∨ (¬ p1204) ∨ (¬ p1205)) : (¬ p1198) ∨ (¬ p1200) ∨ p1193 ∨ p1189 ∨ (¬ p1196) ∨ (¬ p1197) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1198 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1200 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1193) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1196 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1197 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1199) := by
    rcases h7069 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u0)
    · exact q5
    · exact False.elim (q6 u1)
  have u7 : p1201 := by
    rcases h7178 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1202 := by
    rcases h7179 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1203 := by
    rcases h7180 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1204 := by
    rcases h7181 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1205 := by
    rcases h7182 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h7094 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21784 (p1189 p1193 p1196 p1197 p1198 p1200 : Prop)
    (h21779 : p1200 ∨ p1189 ∨ p1193)
    (h21780 : p1196 ∨ p1189 ∨ p1193)
    (h21781 : p1197 ∨ p1189 ∨ p1193)
    (h21782 : p1198 ∨ p1189 ∨ p1193)
    (h21783 : (¬ p1198) ∨ (¬ p1200) ∨ p1193 ∨ p1189 ∨ (¬ p1196) ∨ (¬ p1197)) : p1189 ∨ p1193 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1189) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1193) := fun hu => hn (Or.inr hu)
  have u2 : p1200 := by
    rcases h21779 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1196 := by
    rcases h21780 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1197 := by
    rcases h21781 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1198 := by
    rcases h21782 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21783 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step21785 (p595 p616 p627 p628 p629 p630 p631 p632 : Prop)
    (h3610 : p627 ∨ p628)
    (h3611 : p627 ∨ p629)
    (h3612 : p627 ∨ p630)
    (h3613 : p627 ∨ p631)
    (h3614 : p627 ∨ p632)
    (h3527 : p595 ∨ p616 ∨ (¬ p628) ∨ (¬ p629) ∨ (¬ p630) ∨ (¬ p631) ∨ (¬ p632)) : p627 ∨ p616 ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p627) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p616) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p628 := by
    rcases h3610 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p629 := by
    rcases h3611 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p630 := by
    rcases h3612 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p631 := by
    rcases h3613 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p632 := by
    rcases h3614 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3527 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21786 (p595 p616 p623 p628 p629 p630 p631 p632 : Prop)
    (h3590 : p623 ∨ p628)
    (h3591 : p623 ∨ p629)
    (h3592 : p623 ∨ p630)
    (h3593 : p623 ∨ p631)
    (h3594 : p623 ∨ p632)
    (h3527 : p595 ∨ p616 ∨ (¬ p628) ∨ (¬ p629) ∨ (¬ p630) ∨ (¬ p631) ∨ (¬ p632)) : p623 ∨ p616 ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p623) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p616) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p628 := by
    rcases h3590 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p629 := by
    rcases h3591 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p630 := by
    rcases h3592 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p631 := by
    rcases h3593 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p632 := by
    rcases h3594 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3527 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21787 (p595 p616 p624 p628 p629 p630 p631 p632 : Prop)
    (h3595 : p624 ∨ p628)
    (h3596 : p624 ∨ p629)
    (h3597 : p624 ∨ p630)
    (h3598 : p624 ∨ p631)
    (h3599 : p624 ∨ p632)
    (h3527 : p595 ∨ p616 ∨ (¬ p628) ∨ (¬ p629) ∨ (¬ p630) ∨ (¬ p631) ∨ (¬ p632)) : p624 ∨ p616 ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p624) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p616) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p628 := by
    rcases h3595 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p629 := by
    rcases h3596 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p630 := by
    rcases h3597 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p631 := by
    rcases h3598 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p632 := by
    rcases h3599 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3527 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21788 (p595 p616 p625 p628 p629 p630 p631 p632 : Prop)
    (h3600 : p625 ∨ p628)
    (h3601 : p625 ∨ p629)
    (h3602 : p625 ∨ p630)
    (h3603 : p625 ∨ p631)
    (h3604 : p625 ∨ p632)
    (h3527 : p595 ∨ p616 ∨ (¬ p628) ∨ (¬ p629) ∨ (¬ p630) ∨ (¬ p631) ∨ (¬ p632)) : p625 ∨ p616 ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p625) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p616) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p628 := by
    rcases h3600 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p629 := by
    rcases h3601 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p630 := by
    rcases h3602 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p631 := by
    rcases h3603 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p632 := by
    rcases h3604 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3527 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21789 (p595 p616 p623 p624 p625 p626 p627 p628 p629 p630 p631 p632 : Prop)
    (h3502 : p595 ∨ p616 ∨ (¬ p623) ∨ (¬ p624) ∨ (¬ p625) ∨ (¬ p626) ∨ (¬ p627))
    (h3605 : p626 ∨ p628)
    (h3606 : p626 ∨ p629)
    (h3607 : p626 ∨ p630)
    (h3608 : p626 ∨ p631)
    (h3609 : p626 ∨ p632)
    (h3527 : p595 ∨ p616 ∨ (¬ p628) ∨ (¬ p629) ∨ (¬ p630) ∨ (¬ p631) ∨ (¬ p632)) : (¬ p625) ∨ p616 ∨ p595 ∨ (¬ p627) ∨ (¬ p623) ∨ (¬ p624) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p625 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p616) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p627 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p623 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p624 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p626) := by
    rcases h3502 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u0)
    · exact q5
    · exact False.elim (q6 u3)
  have u7 : p628 := by
    rcases h3605 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p629 := by
    rcases h3606 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p630 := by
    rcases h3607 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p631 := by
    rcases h3608 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p632 := by
    rcases h3609 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h3527 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21790 (p595 p616 p623 p624 p625 p627 : Prop)
    (h21785 : p627 ∨ p616 ∨ p595)
    (h21786 : p623 ∨ p616 ∨ p595)
    (h21787 : p624 ∨ p616 ∨ p595)
    (h21788 : p625 ∨ p616 ∨ p595)
    (h21789 : (¬ p625) ∨ p616 ∨ p595 ∨ (¬ p627) ∨ (¬ p623) ∨ (¬ p624)) : p616 ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p616) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p595) := fun hu => hn (Or.inr hu)
  have u2 : p627 := by
    rcases h21785 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p623 := by
    rcases h21786 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p624 := by
    rcases h21787 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p625 := by
    rcases h21788 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21789 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step21791 (p15 p19 p326 p595 p616 p1189 p1193 : Prop)
    (h9388 : (¬ p15) ∨ p595 ∨ (¬ p1193))
    (h21784 : p1189 ∨ p1193)
    (h16536 : (¬ p15) ∨ (¬ p19) ∨ (¬ p326) ∨ (¬ p616) ∨ (¬ p1189))
    (h21790 : p616 ∨ p595) : p595 ∨ (¬ p19) ∨ (¬ p326) ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p595) := fun hu => hn (Or.inl hu)
  have u1 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p326 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p1193) := by
    rcases h9388 with q0 | q1 | q2
    · exact False.elim (q0 u3)
    · exact False.elim (u0 q1)
    · exact q2
  have u5 : p1189 := by
    rcases h21784 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u6 : (¬ p616) := by
    rcases h16536 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u3)
    · exact False.elim (q1 u1)
    · exact False.elim (q2 u2)
    · exact q3
    · exact False.elim (q4 u5)
  rcases h21790 with q0 | q1
  · exact False.elim (u6 q0)
  · exact False.elim (u0 q1)

theorem step21792 (p1187 p1193 p1199 p1201 p1202 p1203 p1204 p1205 : Prop)
    (h7178 : p1199 ∨ p1201)
    (h7179 : p1199 ∨ p1202)
    (h7180 : p1199 ∨ p1203)
    (h7181 : p1199 ∨ p1204)
    (h7182 : p1199 ∨ p1205)
    (h7099 : p1187 ∨ p1193 ∨ (¬ p1201) ∨ (¬ p1202) ∨ (¬ p1203) ∨ (¬ p1204) ∨ (¬ p1205)) : p1199 ∨ p1187 ∨ p1193 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1199) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1187) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1193) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1201 := by
    rcases h7178 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1202 := by
    rcases h7179 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1203 := by
    rcases h7180 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1204 := by
    rcases h7181 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1205 := by
    rcases h7182 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7099 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21793 (p1187 p1193 p1200 p1201 p1202 p1203 p1204 p1205 : Prop)
    (h7183 : p1200 ∨ p1201)
    (h7184 : p1200 ∨ p1202)
    (h7185 : p1200 ∨ p1203)
    (h7186 : p1200 ∨ p1204)
    (h7187 : p1200 ∨ p1205)
    (h7099 : p1187 ∨ p1193 ∨ (¬ p1201) ∨ (¬ p1202) ∨ (¬ p1203) ∨ (¬ p1204) ∨ (¬ p1205)) : p1200 ∨ p1187 ∨ p1193 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1200) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1187) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1193) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1201 := by
    rcases h7183 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1202 := by
    rcases h7184 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1203 := by
    rcases h7185 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1204 := by
    rcases h7186 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1205 := by
    rcases h7187 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7099 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21794 (p1187 p1193 p1196 p1201 p1202 p1203 p1204 p1205 : Prop)
    (h7163 : p1196 ∨ p1201)
    (h7164 : p1196 ∨ p1202)
    (h7165 : p1196 ∨ p1203)
    (h7166 : p1196 ∨ p1204)
    (h7167 : p1196 ∨ p1205)
    (h7099 : p1187 ∨ p1193 ∨ (¬ p1201) ∨ (¬ p1202) ∨ (¬ p1203) ∨ (¬ p1204) ∨ (¬ p1205)) : p1196 ∨ p1187 ∨ p1193 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1196) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1187) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1193) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1201 := by
    rcases h7163 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1202 := by
    rcases h7164 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1203 := by
    rcases h7165 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1204 := by
    rcases h7166 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1205 := by
    rcases h7167 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7099 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21795 (p1187 p1193 p1197 p1201 p1202 p1203 p1204 p1205 : Prop)
    (h7168 : p1197 ∨ p1201)
    (h7169 : p1197 ∨ p1202)
    (h7170 : p1197 ∨ p1203)
    (h7171 : p1197 ∨ p1204)
    (h7172 : p1197 ∨ p1205)
    (h7099 : p1187 ∨ p1193 ∨ (¬ p1201) ∨ (¬ p1202) ∨ (¬ p1203) ∨ (¬ p1204) ∨ (¬ p1205)) : p1197 ∨ p1187 ∨ p1193 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1197) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1187) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1193) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h7099 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21796 (p1187 p1193 p1196 p1197 p1198 p1199 p1200 p1201 p1202 p1203 p1204 p1205 : Prop)
    (h7074 : p1187 ∨ p1193 ∨ (¬ p1196) ∨ (¬ p1197) ∨ (¬ p1198) ∨ (¬ p1199) ∨ (¬ p1200))
    (h7173 : p1198 ∨ p1201)
    (h7174 : p1198 ∨ p1202)
    (h7175 : p1198 ∨ p1203)
    (h7176 : p1198 ∨ p1204)
    (h7177 : p1198 ∨ p1205)
    (h7099 : p1187 ∨ p1193 ∨ (¬ p1201) ∨ (¬ p1202) ∨ (¬ p1203) ∨ (¬ p1204) ∨ (¬ p1205)) : (¬ p1197) ∨ p1187 ∨ p1193 ∨ (¬ p1199) ∨ (¬ p1200) ∨ (¬ p1196) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1197 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1187) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1193) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1199 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1200 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1196 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1198) := by
    rcases h7074 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u0)
    · exact q4
    · exact False.elim (q5 u3)
    · exact False.elim (q6 u4)
  have u7 : p1201 := by
    rcases h7173 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1202 := by
    rcases h7174 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1203 := by
    rcases h7175 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1204 := by
    rcases h7176 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1205 := by
    rcases h7177 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h7099 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21797 (p1187 p1193 p1196 p1197 p1199 p1200 : Prop)
    (h21792 : p1199 ∨ p1187 ∨ p1193)
    (h21793 : p1200 ∨ p1187 ∨ p1193)
    (h21794 : p1196 ∨ p1187 ∨ p1193)
    (h21795 : p1197 ∨ p1187 ∨ p1193)
    (h21796 : (¬ p1197) ∨ p1187 ∨ p1193 ∨ (¬ p1199) ∨ (¬ p1200) ∨ (¬ p1196)) : p1187 ∨ p1193 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1187) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1193) := fun hu => hn (Or.inr hu)
  have u2 : p1199 := by
    rcases h21792 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1200 := by
    rcases h21793 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1196 := by
    rcases h21794 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1197 := by
    rcases h21795 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21796 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step21798 (p1096 p1099 p1105 p1106 p1107 p1108 p1109 p1113 : Prop)
    (h6582 : p1105 ∨ p1113)
    (h6587 : p1106 ∨ p1113)
    (h6592 : p1107 ∨ p1113)
    (h6597 : p1108 ∨ p1113)
    (h6602 : p1109 ∨ p1113)
    (h6491 : p1096 ∨ p1099 ∨ (¬ p1105) ∨ (¬ p1106) ∨ (¬ p1107) ∨ (¬ p1108) ∨ (¬ p1109)) : p1113 ∨ p1096 ∨ p1099 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1113) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1099) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1105 := by
    rcases h6582 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1106 := by
    rcases h6587 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1107 := by
    rcases h6592 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1108 := by
    rcases h6597 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1109 := by
    rcases h6602 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6491 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21799 (p1096 p1099 p1105 p1106 p1107 p1108 p1109 p1110 : Prop)
    (h6579 : p1105 ∨ p1110)
    (h6584 : p1106 ∨ p1110)
    (h6589 : p1107 ∨ p1110)
    (h6594 : p1108 ∨ p1110)
    (h6599 : p1109 ∨ p1110)
    (h6491 : p1096 ∨ p1099 ∨ (¬ p1105) ∨ (¬ p1106) ∨ (¬ p1107) ∨ (¬ p1108) ∨ (¬ p1109)) : p1110 ∨ p1096 ∨ p1099 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1110) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1099) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1105 := by
    rcases h6579 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1106 := by
    rcases h6584 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1107 := by
    rcases h6589 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1108 := by
    rcases h6594 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1109 := by
    rcases h6599 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6491 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21800 (p1096 p1099 p1105 p1106 p1107 p1108 p1109 p1111 : Prop)
    (h6580 : p1105 ∨ p1111)
    (h6585 : p1106 ∨ p1111)
    (h6590 : p1107 ∨ p1111)
    (h6595 : p1108 ∨ p1111)
    (h6600 : p1109 ∨ p1111)
    (h6491 : p1096 ∨ p1099 ∨ (¬ p1105) ∨ (¬ p1106) ∨ (¬ p1107) ∨ (¬ p1108) ∨ (¬ p1109)) : p1111 ∨ p1096 ∨ p1099 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1111) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1099) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1105 := by
    rcases h6580 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1106 := by
    rcases h6585 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1107 := by
    rcases h6590 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1108 := by
    rcases h6595 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1109 := by
    rcases h6600 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6491 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21801 (p1096 p1099 p1105 p1106 p1107 p1108 p1109 p1110 p1111 p1112 p1113 : Prop)
    (h21323 : p1099 ∨ (¬ p1110) ∨ p1096 ∨ (¬ p1111) ∨ (¬ p1112) ∨ (¬ p1113))
    (h6581 : p1105 ∨ p1112)
    (h6586 : p1106 ∨ p1112)
    (h6591 : p1107 ∨ p1112)
    (h6596 : p1108 ∨ p1112)
    (h6601 : p1109 ∨ p1112)
    (h6491 : p1096 ∨ p1099 ∨ (¬ p1105) ∨ (¬ p1106) ∨ (¬ p1107) ∨ (¬ p1108) ∨ (¬ p1109)) : (¬ p1111) ∨ p1096 ∨ p1099 ∨ (¬ p1113) ∨ (¬ p1110) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1111 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1099) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1113 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p1112) := by
    rcases h21323 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (u2 q0)
    · exact False.elim (q1 u4)
    · exact False.elim (u1 q2)
    · exact False.elim (q3 u0)
    · exact q4
    · exact False.elim (q5 u3)
  have u6 : p1105 := by
    rcases h6581 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u7 : p1106 := by
    rcases h6586 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u8 : p1107 := by
    rcases h6591 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u9 : p1108 := by
    rcases h6596 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p1109 := by
    rcases h6601 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h6491 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u10)

theorem step21802 (p1096 p1099 p1110 p1111 p1113 : Prop)
    (h21798 : p1113 ∨ p1096 ∨ p1099)
    (h21799 : p1110 ∨ p1096 ∨ p1099)
    (h21800 : p1111 ∨ p1096 ∨ p1099)
    (h21801 : (¬ p1111) ∨ p1096 ∨ p1099 ∨ (¬ p1113) ∨ (¬ p1110)) : p1096 ∨ p1099 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1096) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1099) := fun hu => hn (Or.inr hu)
  have u2 : p1113 := by
    rcases h21798 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1110 := by
    rcases h21799 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1111 := by
    rcases h21800 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21801 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)

theorem step21803 (p1229 p1232 p1243 p1244 p1245 p1246 p1247 p1248 : Prop)
    (h7448 : p1243 ∨ p1244)
    (h7449 : p1243 ∨ p1245)
    (h7450 : p1243 ∨ p1246)
    (h7452 : p1243 ∨ p1248)
    (h7365 : p1229 ∨ p1232 ∨ (¬ p1244) ∨ (¬ p1245) ∨ (¬ p1246) ∨ (¬ p1247) ∨ (¬ p1248)) : p1243 ∨ (¬ p1247) ∨ p1229 ∨ p1232 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1243) := fun hu => hn (Or.inl hu)
  have u1 : p1247 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1232) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1244 := by
    rcases h7448 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1245 := by
    rcases h7449 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1246 := by
    rcases h7450 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1248 := by
    rcases h7452 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7365 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step21804 (p18 p24 p32 p33 p34 p35 p36 p37 : Prop)
    (h125 : p32 ∨ p33)
    (h126 : p32 ∨ p34)
    (h127 : p32 ∨ p35)
    (h128 : p32 ∨ p36)
    (h129 : p32 ∨ p37)
    (h40 : p18 ∨ p24 ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p36) ∨ (¬ p37)) : p32 ∨ p24 ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p32) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p24) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p33 := by
    rcases h125 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p34 := by
    rcases h126 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p35 := by
    rcases h127 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p36 := by
    rcases h128 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p37 := by
    rcases h129 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h40 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21805 (p38 p69 p77 p78 p79 p80 p81 p82 : Prop)
    (h389 : p77 ∨ p78)
    (h390 : p77 ∨ p79)
    (h391 : p77 ∨ p80)
    (h392 : p77 ∨ p81)
    (h393 : p77 ∨ p82)
    (h304 : p38 ∨ p69 ∨ (¬ p78) ∨ (¬ p79) ∨ (¬ p80) ∨ (¬ p81) ∨ (¬ p82)) : p77 ∨ p69 ∨ p38 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p77) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p69) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p38) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p78 := by
    rcases h389 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p79 := by
    rcases h390 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p80 := by
    rcases h391 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p81 := by
    rcases h392 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p82 := by
    rcases h393 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h304 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21806 (p38 p69 p76 p78 p79 p80 p81 p82 : Prop)
    (h384 : p76 ∨ p78)
    (h385 : p76 ∨ p79)
    (h386 : p76 ∨ p80)
    (h387 : p76 ∨ p81)
    (h388 : p76 ∨ p82)
    (h304 : p38 ∨ p69 ∨ (¬ p78) ∨ (¬ p79) ∨ (¬ p80) ∨ (¬ p81) ∨ (¬ p82)) : p76 ∨ p69 ∨ p38 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p76) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p69) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p38) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p78 := by
    rcases h384 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
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
  rcases h304 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21807 (p38 p69 p75 p78 p79 p80 p81 p82 : Prop)
    (h379 : p75 ∨ p78)
    (h380 : p75 ∨ p79)
    (h381 : p75 ∨ p80)
    (h382 : p75 ∨ p81)
    (h383 : p75 ∨ p82)
    (h304 : p38 ∨ p69 ∨ (¬ p78) ∨ (¬ p79) ∨ (¬ p80) ∨ (¬ p81) ∨ (¬ p82)) : p75 ∨ p69 ∨ p38 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p75) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p69) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p38) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p78 := by
    rcases h379 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
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
  rcases h304 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21808 (p38 p69 p74 p78 p79 p80 p81 p82 : Prop)
    (h374 : p74 ∨ p78)
    (h375 : p74 ∨ p79)
    (h376 : p74 ∨ p80)
    (h377 : p74 ∨ p81)
    (h378 : p74 ∨ p82)
    (h304 : p38 ∨ p69 ∨ (¬ p78) ∨ (¬ p79) ∨ (¬ p80) ∨ (¬ p81) ∨ (¬ p82)) : p74 ∨ p69 ∨ p38 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p74) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p69) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p38) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p78 := by
    rcases h374 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
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
  rcases h304 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21810 (p15 p69 p73 p74 p75 p76 p77 p78 p79 p80 p81 p82 : Prop)
    (h281 : p15 ∨ p69 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77))
    (h369 : p73 ∨ p78)
    (h370 : p73 ∨ p79)
    (h371 : p73 ∨ p80)
    (h372 : p73 ∨ p81)
    (h373 : p73 ∨ p82)
    (h306 : p15 ∨ p69 ∨ (¬ p78) ∨ (¬ p79) ∨ (¬ p80) ∨ (¬ p81) ∨ (¬ p82)) : (¬ p74) ∨ (¬ p77) ∨ p69 ∨ p15 ∨ (¬ p75) ∨ (¬ p76) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p74 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p77 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p69) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p75 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p76 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p73) := by
    rcases h281 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p78 := by
    rcases h369 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p79 := by
    rcases h370 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p80 := by
    rcases h371 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p81 := by
    rcases h372 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p82 := by
    rcases h373 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h306 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21812 (p139 p142 p148 p149 p150 p151 p152 p153 : Prop)
    (h776 : p148 ∨ p149)
    (h777 : p148 ∨ p150)
    (h778 : p148 ∨ p151)
    (h779 : p148 ∨ p152)
    (h780 : p148 ∨ p153)
    (h703 : p139 ∨ p142 ∨ (¬ p149) ∨ (¬ p150) ∨ (¬ p151) ∨ (¬ p152) ∨ (¬ p153)) : p148 ∨ p139 ∨ p142 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p148) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p139) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p142) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p149 := by
    rcases h776 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p150 := by
    rcases h777 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p151 := by
    rcases h778 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p152 := by
    rcases h779 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p153 := by
    rcases h780 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h703 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21813 (p139 p142 p147 p149 p150 p151 p152 p153 : Prop)
    (h771 : p147 ∨ p149)
    (h772 : p147 ∨ p150)
    (h773 : p147 ∨ p151)
    (h774 : p147 ∨ p152)
    (h775 : p147 ∨ p153)
    (h703 : p139 ∨ p142 ∨ (¬ p149) ∨ (¬ p150) ∨ (¬ p151) ∨ (¬ p152) ∨ (¬ p153)) : p147 ∨ p139 ∨ p142 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p147) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p139) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p142) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p149 := by
    rcases h771 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p150 := by
    rcases h772 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p151 := by
    rcases h773 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p152 := by
    rcases h774 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p153 := by
    rcases h775 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h703 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21814 (p139 p142 p146 p149 p150 p151 p152 p153 : Prop)
    (h766 : p146 ∨ p149)
    (h767 : p146 ∨ p150)
    (h768 : p146 ∨ p151)
    (h769 : p146 ∨ p152)
    (h770 : p146 ∨ p153)
    (h703 : p139 ∨ p142 ∨ (¬ p149) ∨ (¬ p150) ∨ (¬ p151) ∨ (¬ p152) ∨ (¬ p153)) : p146 ∨ p139 ∨ p142 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p146) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p139) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p142) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p149 := by
    rcases h766 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p150 := by
    rcases h767 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p151 := by
    rcases h768 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p152 := by
    rcases h769 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p153 := by
    rcases h770 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h703 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21815 (p139 p142 p145 p149 p150 p151 p152 p153 : Prop)
    (h761 : p145 ∨ p149)
    (h762 : p145 ∨ p150)
    (h763 : p145 ∨ p151)
    (h764 : p145 ∨ p152)
    (h765 : p145 ∨ p153)
    (h703 : p139 ∨ p142 ∨ (¬ p149) ∨ (¬ p150) ∨ (¬ p151) ∨ (¬ p152) ∨ (¬ p153)) : p145 ∨ p139 ∨ p142 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p145) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p139) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p142) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p149 := by
    rcases h761 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p150 := by
    rcases h762 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p151 := by
    rcases h763 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p152 := by
    rcases h764 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p153 := by
    rcases h765 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h703 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21816 (p139 p140 p142 p144 p145 p146 p147 p148 p149 p150 p151 p152 p153 : Prop)
    (h21812 : p148 ∨ p139 ∨ p142)
    (h21813 : p147 ∨ p139 ∨ p142)
    (h21814 : p146 ∨ p139 ∨ p142)
    (h21815 : p145 ∨ p139 ∨ p142)
    (h676 : p139 ∨ p140 ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p147) ∨ (¬ p148))
    (h756 : p144 ∨ p149)
    (h757 : p144 ∨ p150)
    (h758 : p144 ∨ p151)
    (h759 : p144 ∨ p152)
    (h760 : p144 ∨ p153)
    (h703 : p139 ∨ p142 ∨ (¬ p149) ∨ (¬ p150) ∨ (¬ p151) ∨ (¬ p152) ∨ (¬ p153)) : p139 ∨ p140 ∨ p142 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p139) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p140) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p142) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p148 := by
    rcases h21812 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u4 : p147 := by
    rcases h21813 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u5 : p146 := by
    rcases h21814 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u6 : p145 := by
    rcases h21815 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u7 : (¬ p144) := by
    rcases h676 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u0 q0)
    · exact False.elim (u1 q1)
    · exact q2
    · exact False.elim (q3 u6)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u3)
  have u8 : p149 := by
    rcases h756 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p150 := by
    rcases h757 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p151 := by
    rcases h758 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p152 := by
    rcases h759 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u12 : p153 := by
    rcases h760 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h703 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u12)

theorem step21817 (p104 p110 p115 p116 p117 p118 p119 p120 : Prop)
    (h640 : p115 ∨ p116)
    (h641 : p115 ∨ p117)
    (h642 : p115 ∨ p118)
    (h643 : p115 ∨ p119)
    (h644 : p115 ∨ p120)
    (h554 : p104 ∨ p110 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p115 ∨ p104 ∨ p110 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p115) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p104) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p110) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p116 := by
    rcases h640 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p117 := by
    rcases h641 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p118 := by
    rcases h642 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p119 := by
    rcases h643 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p120 := by
    rcases h644 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h554 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21818 (p104 p110 p114 p116 p117 p118 p119 p120 : Prop)
    (h635 : p114 ∨ p116)
    (h636 : p114 ∨ p117)
    (h637 : p114 ∨ p118)
    (h638 : p114 ∨ p119)
    (h639 : p114 ∨ p120)
    (h554 : p104 ∨ p110 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p114 ∨ p104 ∨ p110 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p114) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p104) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p110) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p116 := by
    rcases h635 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p117 := by
    rcases h636 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p118 := by
    rcases h637 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p119 := by
    rcases h638 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p120 := by
    rcases h639 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h554 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21819 (p104 p110 p113 p116 p117 p118 p119 p120 : Prop)
    (h630 : p113 ∨ p116)
    (h631 : p113 ∨ p117)
    (h632 : p113 ∨ p118)
    (h633 : p113 ∨ p119)
    (h634 : p113 ∨ p120)
    (h554 : p104 ∨ p110 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p113 ∨ p104 ∨ p110 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p113) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p104) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p110) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p116 := by
    rcases h630 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p117 := by
    rcases h631 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p118 := by
    rcases h632 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p119 := by
    rcases h633 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p120 := by
    rcases h634 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h554 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21820 (p104 p110 p112 p116 p117 p118 p119 p120 : Prop)
    (h625 : p112 ∨ p116)
    (h626 : p112 ∨ p117)
    (h627 : p112 ∨ p118)
    (h628 : p112 ∨ p119)
    (h629 : p112 ∨ p120)
    (h554 : p104 ∨ p110 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p112 ∨ p104 ∨ p110 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p112) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p104) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p110) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p116 := by
    rcases h625 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p117 := by
    rcases h626 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p118 := by
    rcases h627 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p119 := by
    rcases h628 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p120 := by
    rcases h629 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h554 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21822 (p139 p140 p142 : Prop)
    (h16166 : p139 ∨ (¬ p142))
    (h21816 : p139 ∨ p140 ∨ p142) : p139 ∨ p140 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p139) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p140) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p142) := by
    rcases h16166 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h21816 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (u2 q2)

theorem step21823 (p11 p18 p19 p139 p423 p1206 p1207 p1211 : Prop)
    (h4 : (¬ p18) ∨ (¬ p19))
    (h14536 : p19 ∨ (¬ p423) ∨ (¬ p1207))
    (h16439 : (¬ p11) ∨ (¬ p18) ∨ (¬ p139) ∨ (¬ p423) ∨ (¬ p1211))
    (h21629 : p1211 ∨ p1207 ∨ p1206) : (¬ p423) ∨ p1206 ∨ (¬ p139) ∨ (¬ p11) ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1206) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p139 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p19) := by
    rcases h4 with q0 | q1
    · exact False.elim (q0 u4)
    · exact q1
  have u6 : (¬ p1207) := by
    rcases h14536 with q0 | q1 | q2
    · exact False.elim (u5 q0)
    · exact False.elim (q1 u0)
    · exact q2
  have u7 : (¬ p1211) := by
    rcases h16439 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u3)
    · exact False.elim (q1 u4)
    · exact False.elim (q2 u2)
    · exact False.elim (q3 u0)
    · exact q4
  rcases h21629 with q0 | q1 | q2
  · exact False.elim (u7 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (u1 q2)

theorem step21829 (p14 p229 p891 p892 p893 p894 p895 p896 : Prop)
    (h5195 : p891 ∨ p892)
    (h5196 : p891 ∨ p893)
    (h5197 : p891 ∨ p894)
    (h5198 : p891 ∨ p895)
    (h5199 : p891 ∨ p896)
    (h5112 : p14 ∨ p229 ∨ (¬ p892) ∨ (¬ p893) ∨ (¬ p894) ∨ (¬ p895) ∨ (¬ p896)) : p891 ∨ p229 ∨ p14 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p891) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p14) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p892 := by
    rcases h5195 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p893 := by
    rcases h5196 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p894 := by
    rcases h5197 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p895 := by
    rcases h5198 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p896 := by
    rcases h5199 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5112 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21830 (p14 p229 p890 p892 p893 p894 p895 p896 : Prop)
    (h5190 : p890 ∨ p892)
    (h5191 : p890 ∨ p893)
    (h5192 : p890 ∨ p894)
    (h5193 : p890 ∨ p895)
    (h5194 : p890 ∨ p896)
    (h5112 : p14 ∨ p229 ∨ (¬ p892) ∨ (¬ p893) ∨ (¬ p894) ∨ (¬ p895) ∨ (¬ p896)) : p890 ∨ p229 ∨ p14 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p890) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p14) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p892 := by
    rcases h5190 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p893 := by
    rcases h5191 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p894 := by
    rcases h5192 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p895 := by
    rcases h5193 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p896 := by
    rcases h5194 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5112 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21831 (p14 p229 p889 p892 p893 p894 p895 p896 : Prop)
    (h5185 : p889 ∨ p892)
    (h5186 : p889 ∨ p893)
    (h5187 : p889 ∨ p894)
    (h5188 : p889 ∨ p895)
    (h5189 : p889 ∨ p896)
    (h5112 : p14 ∨ p229 ∨ (¬ p892) ∨ (¬ p893) ∨ (¬ p894) ∨ (¬ p895) ∨ (¬ p896)) : p889 ∨ p229 ∨ p14 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p889) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p14) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p892 := by
    rcases h5185 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p893 := by
    rcases h5186 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p894 := by
    rcases h5187 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p895 := by
    rcases h5188 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p896 := by
    rcases h5189 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5112 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21832 (p14 p229 p888 p892 p893 p894 p895 p896 : Prop)
    (h5180 : p888 ∨ p892)
    (h5181 : p888 ∨ p893)
    (h5182 : p888 ∨ p894)
    (h5183 : p888 ∨ p895)
    (h5184 : p888 ∨ p896)
    (h5112 : p14 ∨ p229 ∨ (¬ p892) ∨ (¬ p893) ∨ (¬ p894) ∨ (¬ p895) ∨ (¬ p896)) : p888 ∨ p229 ∨ p14 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p888) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p14) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p892 := by
    rcases h5180 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p893 := by
    rcases h5181 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p894 := by
    rcases h5182 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p895 := by
    rcases h5183 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p896 := by
    rcases h5184 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5112 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21833 (p14 p229 p887 p888 p889 p890 p891 p892 p893 p894 p895 p896 : Prop)
    (h5087 : p14 ∨ p229 ∨ (¬ p887) ∨ (¬ p888) ∨ (¬ p889) ∨ (¬ p890) ∨ (¬ p891))
    (h5175 : p887 ∨ p892)
    (h5176 : p887 ∨ p893)
    (h5177 : p887 ∨ p894)
    (h5178 : p887 ∨ p895)
    (h5179 : p887 ∨ p896)
    (h5112 : p14 ∨ p229 ∨ (¬ p892) ∨ (¬ p893) ∨ (¬ p894) ∨ (¬ p895) ∨ (¬ p896)) : (¬ p888) ∨ (¬ p891) ∨ p14 ∨ p229 ∨ (¬ p889) ∨ (¬ p890) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p888 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p891 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p889 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p890 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p887) := by
    rcases h5087 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p892 := by
    rcases h5175 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p893 := by
    rcases h5176 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p894 := by
    rcases h5177 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p895 := by
    rcases h5178 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p896 := by
    rcases h5179 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h5112 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21834 (p14 p229 p888 p889 p890 p891 : Prop)
    (h21829 : p891 ∨ p229 ∨ p14)
    (h21830 : p890 ∨ p229 ∨ p14)
    (h21831 : p889 ∨ p229 ∨ p14)
    (h21832 : p888 ∨ p229 ∨ p14)
    (h21833 : (¬ p888) ∨ (¬ p891) ∨ p14 ∨ p229 ∨ (¬ p889) ∨ (¬ p890)) : p229 ∨ p14 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p229) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p14) := fun hu => hn (Or.inr hu)
  have u2 : p891 := by
    rcases h21829 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p890 := by
    rcases h21830 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p889 := by
    rcases h21831 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p888 := by
    rcases h21832 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21833 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step21835 (p1036 p1044 p1049 p1050 p1051 p1052 p1053 p1054 : Prop)
    (h6216 : p1049 ∨ p1050)
    (h6217 : p1049 ∨ p1051)
    (h6218 : p1049 ∨ p1052)
    (h6219 : p1049 ∨ p1053)
    (h6220 : p1049 ∨ p1054)
    (h6135 : p1036 ∨ p1044 ∨ (¬ p1050) ∨ (¬ p1051) ∨ (¬ p1052) ∨ (¬ p1053) ∨ (¬ p1054)) : p1049 ∨ p1044 ∨ p1036 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1049) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1044) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1036) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1050 := by
    rcases h6216 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1051 := by
    rcases h6217 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1052 := by
    rcases h6218 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1053 := by
    rcases h6219 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1054 := by
    rcases h6220 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6135 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21836 (p1036 p1044 p1048 p1050 p1051 p1052 p1053 p1054 : Prop)
    (h6211 : p1048 ∨ p1050)
    (h6212 : p1048 ∨ p1051)
    (h6213 : p1048 ∨ p1052)
    (h6214 : p1048 ∨ p1053)
    (h6215 : p1048 ∨ p1054)
    (h6135 : p1036 ∨ p1044 ∨ (¬ p1050) ∨ (¬ p1051) ∨ (¬ p1052) ∨ (¬ p1053) ∨ (¬ p1054)) : p1048 ∨ p1044 ∨ p1036 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1048) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1044) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1036) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1050 := by
    rcases h6211 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1051 := by
    rcases h6212 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1052 := by
    rcases h6213 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1053 := by
    rcases h6214 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1054 := by
    rcases h6215 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6135 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21837 (p1036 p1044 p1047 p1050 p1051 p1052 p1053 p1054 : Prop)
    (h6206 : p1047 ∨ p1050)
    (h6207 : p1047 ∨ p1051)
    (h6208 : p1047 ∨ p1052)
    (h6209 : p1047 ∨ p1053)
    (h6210 : p1047 ∨ p1054)
    (h6135 : p1036 ∨ p1044 ∨ (¬ p1050) ∨ (¬ p1051) ∨ (¬ p1052) ∨ (¬ p1053) ∨ (¬ p1054)) : p1047 ∨ p1044 ∨ p1036 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1047) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1044) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1036) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1050 := by
    rcases h6206 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1051 := by
    rcases h6207 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1052 := by
    rcases h6208 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1053 := by
    rcases h6209 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1054 := by
    rcases h6210 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6135 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21838 (p1036 p1044 p1046 p1050 p1051 p1052 p1053 p1054 : Prop)
    (h6201 : p1046 ∨ p1050)
    (h6202 : p1046 ∨ p1051)
    (h6203 : p1046 ∨ p1052)
    (h6204 : p1046 ∨ p1053)
    (h6205 : p1046 ∨ p1054)
    (h6135 : p1036 ∨ p1044 ∨ (¬ p1050) ∨ (¬ p1051) ∨ (¬ p1052) ∨ (¬ p1053) ∨ (¬ p1054)) : p1046 ∨ p1044 ∨ p1036 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1046) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1044) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1036) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1050 := by
    rcases h6201 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1051 := by
    rcases h6202 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1052 := by
    rcases h6203 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1053 := by
    rcases h6204 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1054 := by
    rcases h6205 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6135 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21839 (p1036 p1044 p1045 p1046 p1047 p1048 p1049 p1050 p1051 p1052 p1053 p1054 : Prop)
    (h6110 : p1036 ∨ p1044 ∨ (¬ p1045) ∨ (¬ p1046) ∨ (¬ p1047) ∨ (¬ p1048) ∨ (¬ p1049))
    (h6196 : p1045 ∨ p1050)
    (h6197 : p1045 ∨ p1051)
    (h6198 : p1045 ∨ p1052)
    (h6199 : p1045 ∨ p1053)
    (h6200 : p1045 ∨ p1054)
    (h6135 : p1036 ∨ p1044 ∨ (¬ p1050) ∨ (¬ p1051) ∨ (¬ p1052) ∨ (¬ p1053) ∨ (¬ p1054)) : (¬ p1046) ∨ (¬ p1049) ∨ p1036 ∨ p1044 ∨ (¬ p1047) ∨ (¬ p1048) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1046 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1049 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1036) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1044) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1047 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1048 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1045) := by
    rcases h6110 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p1050 := by
    rcases h6196 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1051 := by
    rcases h6197 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1052 := by
    rcases h6198 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1053 := by
    rcases h6199 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1054 := by
    rcases h6200 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h6135 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

#print axioms step21839

end NineRUPTrial
