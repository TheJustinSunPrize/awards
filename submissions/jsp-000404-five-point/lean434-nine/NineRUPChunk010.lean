import Mathlib.Tactic.Tauto

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

namespace NineRUPTrial

theorem step21840 (p1036 p1044 p1046 p1047 p1048 p1049 : Prop)
    (h21835 : p1049 ∨ p1044 ∨ p1036)
    (h21836 : p1048 ∨ p1044 ∨ p1036)
    (h21837 : p1047 ∨ p1044 ∨ p1036)
    (h21838 : p1046 ∨ p1044 ∨ p1036)
    (h21839 : (¬ p1046) ∨ (¬ p1049) ∨ p1036 ∨ p1044 ∨ (¬ p1047) ∨ (¬ p1048)) : p1044 ∨ p1036 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1044) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1036) := fun hu => hn (Or.inr hu)
  have u2 : p1049 := by
    rcases h21835 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1048 := by
    rcases h21836 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1047 := by
    rcases h21837 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1046 := by
    rcases h21838 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21839 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step21841 (p63 p87 p95 p96 p97 p98 p99 p100 : Prop)
    (h514 : p95 ∨ p96)
    (h515 : p95 ∨ p97)
    (h516 : p95 ∨ p98)
    (h517 : p95 ∨ p99)
    (h518 : p95 ∨ p100)
    (h441 : p63 ∨ p87 ∨ (¬ p96) ∨ (¬ p97) ∨ (¬ p98) ∨ (¬ p99) ∨ (¬ p100)) : p95 ∨ p87 ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p95) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p87) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p96 := by
    rcases h514 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p97 := by
    rcases h515 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p98 := by
    rcases h516 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p99 := by
    rcases h517 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p100 := by
    rcases h518 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h441 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21842 (p63 p87 p94 p96 p97 p98 p99 p100 : Prop)
    (h509 : p94 ∨ p96)
    (h510 : p94 ∨ p97)
    (h511 : p94 ∨ p98)
    (h512 : p94 ∨ p99)
    (h513 : p94 ∨ p100)
    (h441 : p63 ∨ p87 ∨ (¬ p96) ∨ (¬ p97) ∨ (¬ p98) ∨ (¬ p99) ∨ (¬ p100)) : p94 ∨ p87 ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p94) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p87) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p96 := by
    rcases h509 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p97 := by
    rcases h510 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p98 := by
    rcases h511 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p99 := by
    rcases h512 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p100 := by
    rcases h513 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h441 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21843 (p63 p87 p93 p96 p97 p98 p99 p100 : Prop)
    (h504 : p93 ∨ p96)
    (h505 : p93 ∨ p97)
    (h506 : p93 ∨ p98)
    (h507 : p93 ∨ p99)
    (h508 : p93 ∨ p100)
    (h441 : p63 ∨ p87 ∨ (¬ p96) ∨ (¬ p97) ∨ (¬ p98) ∨ (¬ p99) ∨ (¬ p100)) : p93 ∨ p87 ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p93) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p87) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p96 := by
    rcases h504 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p97 := by
    rcases h505 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p98 := by
    rcases h506 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p99 := by
    rcases h507 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p100 := by
    rcases h508 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h441 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21844 (p63 p87 p92 p96 p97 p98 p99 p100 : Prop)
    (h499 : p92 ∨ p96)
    (h500 : p92 ∨ p97)
    (h501 : p92 ∨ p98)
    (h502 : p92 ∨ p99)
    (h503 : p92 ∨ p100)
    (h441 : p63 ∨ p87 ∨ (¬ p96) ∨ (¬ p97) ∨ (¬ p98) ∨ (¬ p99) ∨ (¬ p100)) : p92 ∨ p87 ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p92) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p87) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p96 := by
    rcases h499 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p97 := by
    rcases h500 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p98 := by
    rcases h501 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p99 := by
    rcases h502 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p100 := by
    rcases h503 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h441 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21845 (p17 p63 p87 p88 p91 p92 p93 p94 p95 p96 p97 p98 p99 p100 p258 p574 p580 p581 p633 : Prop)
    (h8745 : (¬ p258) ∨ (¬ p574) ∨ (¬ p633))
    (h21467 : p581 ∨ p574)
    (h20972 : p574 ∨ p580)
    (h8740 : (¬ p17) ∨ (¬ p88) ∨ (¬ p581))
    (h19260 : (¬ p17) ∨ (¬ p87) ∨ (¬ p258) ∨ (¬ p580) ∨ (¬ p633))
    (h21841 : p95 ∨ p87 ∨ p63)
    (h21842 : p94 ∨ p87 ∨ p63)
    (h21843 : p93 ∨ p87 ∨ p63)
    (h21844 : p92 ∨ p87 ∨ p63)
    (h414 : p87 ∨ p88 ∨ (¬ p91) ∨ (¬ p92) ∨ (¬ p93) ∨ (¬ p94) ∨ (¬ p95))
    (h494 : p91 ∨ p96)
    (h495 : p91 ∨ p97)
    (h496 : p91 ∨ p98)
    (h497 : p91 ∨ p99)
    (h498 : p91 ∨ p100)
    (h441 : p63 ∨ p87 ∨ (¬ p96) ∨ (¬ p97) ∨ (¬ p98) ∨ (¬ p99) ∨ (¬ p100)) : (¬ p17) ∨ p63 ∨ (¬ p258) ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p63) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p574) := by
    rcases h8745 with q0 | q1 | q2
    · exact False.elim (q0 u2)
    · exact q1
    · exact False.elim (q2 u3)
  have u5 : p581 := by
    rcases h21467 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u6 : p580 := by
    rcases h20972 with q0 | q1
    · exact False.elim (u4 q0)
    · exact q1
  have u7 : (¬ p88) := by
    rcases h8740 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (q2 u5)
  have u8 : (¬ p87) := by
    rcases h19260 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (q2 u2)
    · exact False.elim (q3 u6)
    · exact False.elim (q4 u3)
  have u9 : p95 := by
    rcases h21841 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u8 q1)
    · exact False.elim (u1 q2)
  have u10 : p94 := by
    rcases h21842 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u8 q1)
    · exact False.elim (u1 q2)
  have u11 : p93 := by
    rcases h21843 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u8 q1)
    · exact False.elim (u1 q2)
  have u12 : p92 := by
    rcases h21844 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u8 q1)
    · exact False.elim (u1 q2)
  have u13 : (¬ p91) := by
    rcases h414 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u8 q0)
    · exact False.elim (u7 q1)
    · exact q2
    · exact False.elim (q3 u12)
    · exact False.elim (q4 u11)
    · exact False.elim (q5 u10)
    · exact False.elim (q6 u9)
  have u14 : p96 := by
    rcases h494 with q0 | q1
    · exact False.elim (u13 q0)
    · exact q1
  have u15 : p97 := by
    rcases h495 with q0 | q1
    · exact False.elim (u13 q0)
    · exact q1
  have u16 : p98 := by
    rcases h496 with q0 | q1
    · exact False.elim (u13 q0)
    · exact q1
  have u17 : p99 := by
    rcases h497 with q0 | q1
    · exact False.elim (u13 q0)
    · exact q1
  have u18 : p100 := by
    rcases h498 with q0 | q1
    · exact False.elim (u13 q0)
    · exact q1
  rcases h441 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u14)
  · exact False.elim (q3 u15)
  · exact False.elim (q4 u16)
  · exact False.elim (q5 u17)
  · exact False.elim (q6 u18)

theorem step21846 (p17 p185 p255 p256 p287 p288 p583 p633 : Prop)
    (h21276 : p256 ∨ p17)
    (h1952 : p17 ∨ (¬ p185) ∨ (¬ p287))
    (h16313 : (¬ p185) ∨ (¬ p255) ∨ (¬ p256) ∨ (¬ p583) ∨ (¬ p633))
    (h21419 : p255 ∨ p287 ∨ p288) : (¬ p185) ∨ p17 ∨ (¬ p583) ∨ p288 ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p583 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p288) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p256 := by
    rcases h21276 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : (¬ p287) := by
    rcases h1952 with q0 | q1 | q2
    · exact False.elim (u1 q0)
    · exact False.elim (q1 u0)
    · exact q2
  have u7 : (¬ p255) := by
    rcases h16313 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u2)
    · exact False.elim (q4 u4)
  rcases h21419 with q0 | q1 | q2
  · exact False.elim (u7 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (u3 q2)

theorem step21847 (p63 p86 p95 p96 p97 p98 p99 p100 : Prop)
    (h514 : p95 ∨ p96)
    (h515 : p95 ∨ p97)
    (h516 : p95 ∨ p98)
    (h517 : p95 ∨ p99)
    (h518 : p95 ∨ p100)
    (h436 : p63 ∨ p86 ∨ (¬ p96) ∨ (¬ p97) ∨ (¬ p98) ∨ (¬ p99) ∨ (¬ p100)) : p95 ∨ p86 ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p95) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p86) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p96 := by
    rcases h514 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p97 := by
    rcases h515 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p98 := by
    rcases h516 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p99 := by
    rcases h517 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p100 := by
    rcases h518 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h436 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21848 (p63 p86 p94 p96 p97 p98 p99 p100 : Prop)
    (h509 : p94 ∨ p96)
    (h510 : p94 ∨ p97)
    (h511 : p94 ∨ p98)
    (h512 : p94 ∨ p99)
    (h513 : p94 ∨ p100)
    (h436 : p63 ∨ p86 ∨ (¬ p96) ∨ (¬ p97) ∨ (¬ p98) ∨ (¬ p99) ∨ (¬ p100)) : p94 ∨ p86 ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p94) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p86) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p96 := by
    rcases h509 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p97 := by
    rcases h510 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p98 := by
    rcases h511 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p99 := by
    rcases h512 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p100 := by
    rcases h513 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h436 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21849 (p63 p86 p93 p96 p97 p98 p99 p100 : Prop)
    (h504 : p93 ∨ p96)
    (h505 : p93 ∨ p97)
    (h506 : p93 ∨ p98)
    (h507 : p93 ∨ p99)
    (h508 : p93 ∨ p100)
    (h436 : p63 ∨ p86 ∨ (¬ p96) ∨ (¬ p97) ∨ (¬ p98) ∨ (¬ p99) ∨ (¬ p100)) : p93 ∨ p86 ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p93) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p86) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p96 := by
    rcases h504 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p97 := by
    rcases h505 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p98 := by
    rcases h506 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p99 := by
    rcases h507 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p100 := by
    rcases h508 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h436 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21850 (p63 p86 p92 p96 p97 p98 p99 p100 : Prop)
    (h499 : p92 ∨ p96)
    (h500 : p92 ∨ p97)
    (h501 : p92 ∨ p98)
    (h502 : p92 ∨ p99)
    (h503 : p92 ∨ p100)
    (h436 : p63 ∨ p86 ∨ (¬ p96) ∨ (¬ p97) ∨ (¬ p98) ∨ (¬ p99) ∨ (¬ p100)) : p92 ∨ p86 ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p92) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p86) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p96 := by
    rcases h499 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p97 := by
    rcases h500 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p98 := by
    rcases h501 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p99 := by
    rcases h502 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p100 := by
    rcases h503 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h436 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21851 (p63 p86 p91 p92 p93 p94 p95 p96 p97 p98 p99 p100 : Prop)
    (h411 : p63 ∨ p86 ∨ (¬ p91) ∨ (¬ p92) ∨ (¬ p93) ∨ (¬ p94) ∨ (¬ p95))
    (h494 : p91 ∨ p96)
    (h495 : p91 ∨ p97)
    (h496 : p91 ∨ p98)
    (h497 : p91 ∨ p99)
    (h498 : p91 ∨ p100)
    (h436 : p63 ∨ p86 ∨ (¬ p96) ∨ (¬ p97) ∨ (¬ p98) ∨ (¬ p99) ∨ (¬ p100)) : (¬ p92) ∨ (¬ p95) ∨ p63 ∨ p86 ∨ (¬ p93) ∨ (¬ p94) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p92 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p95 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p86) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p93 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p94 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p91) := by
    rcases h411 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p96 := by
    rcases h494 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p97 := by
    rcases h495 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p98 := by
    rcases h496 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p99 := by
    rcases h497 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p100 := by
    rcases h498 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h436 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21852 (p63 p86 p92 p93 p94 p95 : Prop)
    (h21847 : p95 ∨ p86 ∨ p63)
    (h21848 : p94 ∨ p86 ∨ p63)
    (h21849 : p93 ∨ p86 ∨ p63)
    (h21850 : p92 ∨ p86 ∨ p63)
    (h21851 : (¬ p92) ∨ (¬ p95) ∨ p63 ∨ p86 ∨ (¬ p93) ∨ (¬ p94)) : p86 ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p86) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p63) := fun hu => hn (Or.inr hu)
  have u2 : p95 := by
    rcases h21847 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p94 := by
    rcases h21848 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p93 := by
    rcases h21849 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p92 := by
    rcases h21850 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21851 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step21853 (p1115 p1116 p1129 p1130 p1131 p1132 p1133 p1134 : Prop)
    (h6728 : p1129 ∨ p1130)
    (h6729 : p1129 ∨ p1131)
    (h6730 : p1129 ∨ p1132)
    (h6731 : p1129 ∨ p1133)
    (h6732 : p1129 ∨ p1134)
    (h6645 : p1115 ∨ p1116 ∨ (¬ p1130) ∨ (¬ p1131) ∨ (¬ p1132) ∨ (¬ p1133) ∨ (¬ p1134)) : p1129 ∨ p1115 ∨ p1116 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1129) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1115) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1116) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1130 := by
    rcases h6728 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1131 := by
    rcases h6729 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1132 := by
    rcases h6730 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1133 := by
    rcases h6731 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1134 := by
    rcases h6732 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6645 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21854 (p1115 p1116 p1128 p1130 p1131 p1132 p1133 p1134 : Prop)
    (h6723 : p1128 ∨ p1130)
    (h6724 : p1128 ∨ p1131)
    (h6725 : p1128 ∨ p1132)
    (h6726 : p1128 ∨ p1133)
    (h6727 : p1128 ∨ p1134)
    (h6645 : p1115 ∨ p1116 ∨ (¬ p1130) ∨ (¬ p1131) ∨ (¬ p1132) ∨ (¬ p1133) ∨ (¬ p1134)) : p1128 ∨ p1115 ∨ p1116 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1128) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1115) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h6645 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21855 (p1115 p1116 p1127 p1130 p1131 p1132 p1133 p1134 : Prop)
    (h6718 : p1127 ∨ p1130)
    (h6719 : p1127 ∨ p1131)
    (h6720 : p1127 ∨ p1132)
    (h6721 : p1127 ∨ p1133)
    (h6722 : p1127 ∨ p1134)
    (h6645 : p1115 ∨ p1116 ∨ (¬ p1130) ∨ (¬ p1131) ∨ (¬ p1132) ∨ (¬ p1133) ∨ (¬ p1134)) : p1127 ∨ p1115 ∨ p1116 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1127) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1115) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1116) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h6645 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21856 (p1115 p1116 p1126 p1130 p1131 p1132 p1133 p1134 : Prop)
    (h6713 : p1126 ∨ p1130)
    (h6714 : p1126 ∨ p1131)
    (h6715 : p1126 ∨ p1132)
    (h6716 : p1126 ∨ p1133)
    (h6717 : p1126 ∨ p1134)
    (h6645 : p1115 ∨ p1116 ∨ (¬ p1130) ∨ (¬ p1131) ∨ (¬ p1132) ∨ (¬ p1133) ∨ (¬ p1134)) : p1126 ∨ p1115 ∨ p1116 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1126) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1115) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1116) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h6645 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21857 (p1115 p1116 p1125 p1126 p1127 p1128 p1129 p1130 p1131 p1132 p1133 p1134 : Prop)
    (h6620 : p1115 ∨ p1116 ∨ (¬ p1125) ∨ (¬ p1126) ∨ (¬ p1127) ∨ (¬ p1128) ∨ (¬ p1129))
    (h6708 : p1125 ∨ p1130)
    (h6709 : p1125 ∨ p1131)
    (h6710 : p1125 ∨ p1132)
    (h6711 : p1125 ∨ p1133)
    (h6712 : p1125 ∨ p1134)
    (h6645 : p1115 ∨ p1116 ∨ (¬ p1130) ∨ (¬ p1131) ∨ (¬ p1132) ∨ (¬ p1133) ∨ (¬ p1134)) : (¬ p1126) ∨ p1115 ∨ p1116 ∨ (¬ p1127) ∨ (¬ p1128) ∨ (¬ p1129) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1115) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1116) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1128 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1129 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1125) := by
    rcases h6620 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u2 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u5)
  have u7 : p1130 := by
    rcases h6708 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1131 := by
    rcases h6709 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1132 := by
    rcases h6710 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1133 := by
    rcases h6711 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1134 := by
    rcases h6712 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h6645 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21858 (p1115 p1116 p1126 p1127 p1128 p1129 : Prop)
    (h21853 : p1129 ∨ p1115 ∨ p1116)
    (h21854 : p1128 ∨ p1115 ∨ p1116)
    (h21855 : p1127 ∨ p1115 ∨ p1116)
    (h21856 : p1126 ∨ p1115 ∨ p1116)
    (h21857 : (¬ p1126) ∨ p1115 ∨ p1116 ∨ (¬ p1127) ∨ (¬ p1128) ∨ (¬ p1129)) : p1115 ∨ p1116 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1115) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1116) := fun hu => hn (Or.inr hu)
  have u2 : p1129 := by
    rcases h21853 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1128 := by
    rcases h21854 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1127 := by
    rcases h21855 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1126 := by
    rcases h21856 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21857 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u2)

theorem step21859 (p283 p288 p295 p296 p297 p298 p299 p300 : Prop)
    (h1566 : p295 ∨ p296)
    (h1567 : p295 ∨ p297)
    (h1568 : p295 ∨ p298)
    (h1569 : p295 ∨ p299)
    (h1570 : p295 ∨ p300)
    (h1473 : p283 ∨ p288 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300)) : p295 ∨ p283 ∨ p288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p295) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p283) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p288) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p296 := by
    rcases h1566 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p297 := by
    rcases h1567 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p298 := by
    rcases h1568 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p299 := by
    rcases h1569 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p300 := by
    rcases h1570 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1473 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21860 (p283 p288 p294 p296 p297 p298 p299 p300 : Prop)
    (h1561 : p294 ∨ p296)
    (h1562 : p294 ∨ p297)
    (h1563 : p294 ∨ p298)
    (h1564 : p294 ∨ p299)
    (h1565 : p294 ∨ p300)
    (h1473 : p283 ∨ p288 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300)) : p294 ∨ p283 ∨ p288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p294) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p283) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p288) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p296 := by
    rcases h1561 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p297 := by
    rcases h1562 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p298 := by
    rcases h1563 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p299 := by
    rcases h1564 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p300 := by
    rcases h1565 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1473 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21861 (p283 p288 p293 p296 p297 p298 p299 p300 : Prop)
    (h1556 : p293 ∨ p296)
    (h1557 : p293 ∨ p297)
    (h1558 : p293 ∨ p298)
    (h1559 : p293 ∨ p299)
    (h1560 : p293 ∨ p300)
    (h1473 : p283 ∨ p288 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300)) : p293 ∨ p283 ∨ p288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p293) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p283) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p288) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p296 := by
    rcases h1556 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p297 := by
    rcases h1557 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p298 := by
    rcases h1558 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p299 := by
    rcases h1559 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p300 := by
    rcases h1560 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1473 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21862 (p283 p288 p292 p296 p297 p298 p299 p300 : Prop)
    (h1551 : p292 ∨ p296)
    (h1552 : p292 ∨ p297)
    (h1553 : p292 ∨ p298)
    (h1554 : p292 ∨ p299)
    (h1555 : p292 ∨ p300)
    (h1473 : p283 ∨ p288 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300)) : p292 ∨ p283 ∨ p288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p292) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p283) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p288) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p296 := by
    rcases h1551 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p297 := by
    rcases h1552 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p298 := by
    rcases h1553 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p299 := by
    rcases h1554 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p300 := by
    rcases h1555 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1473 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21863 (p283 p288 p291 p296 p297 p298 p299 p300 : Prop)
    (h1546 : p291 ∨ p296)
    (h1547 : p291 ∨ p297)
    (h1548 : p291 ∨ p298)
    (h1549 : p291 ∨ p299)
    (h1550 : p291 ∨ p300)
    (h1473 : p283 ∨ p288 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300)) : p291 ∨ p283 ∨ p288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p291) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p283) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p288) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p296 := by
    rcases h1546 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p297 := by
    rcases h1547 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p298 := by
    rcases h1548 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p299 := by
    rcases h1549 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p300 := by
    rcases h1550 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1473 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21864 (p283 p288 p291 p292 p293 p294 p295 : Prop)
    (h21859 : p295 ∨ p283 ∨ p288)
    (h21860 : p294 ∨ p283 ∨ p288)
    (h21861 : p293 ∨ p283 ∨ p288)
    (h21862 : p292 ∨ p283 ∨ p288)
    (h21863 : p291 ∨ p283 ∨ p288)
    (h1448 : p283 ∨ p288 ∨ (¬ p291) ∨ (¬ p292) ∨ (¬ p293) ∨ (¬ p294) ∨ (¬ p295)) : p283 ∨ p288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p283) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p288) := fun hu => hn (Or.inr hu)
  have u2 : p295 := by
    rcases h21859 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p294 := by
    rcases h21860 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p293 := by
    rcases h21861 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p292 := by
    rcases h21862 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p291 := by
    rcases h21863 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h1448 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u2)

theorem step21866 (p11 p258 p286 p287 p288 p1077 p1079 p1083 p1116 p1443 : Prop)
    (h9412 : (¬ p11) ∨ (¬ p1443))
    (h21140 : p286 ∨ p258)
    (h21436 : p258 ∨ p287)
    (h21668 : p258 ∨ p288)
    (h13257 : (¬ p286) ∨ (¬ p1077) ∨ p1116)
    (h12419 : (¬ p11) ∨ (¬ p287) ∨ (¬ p1079) ∨ (¬ p1116))
    (h12290 : (¬ p288) ∨ (¬ p1083) ∨ p1443)
    (h20699 : p1079 ∨ p1083) : p258 ∨ (¬ p1077) ∨ (¬ p11) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p258) := fun hu => hn (Or.inl hu)
  have u1 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1443) := by
    rcases h9412 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u4 : p286 := by
    rcases h21140 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p287 := by
    rcases h21436 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p288 := by
    rcases h21668 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1116 := by
    rcases h13257 with q0 | q1 | q2
    · exact False.elim (q0 u4)
    · exact False.elim (q1 u1)
    · exact q2
  have u8 : (¬ p1079) := by
    rcases h12419 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u2)
    · exact False.elim (q1 u5)
    · exact q2
    · exact False.elim (q3 u7)
  have u9 : (¬ p1083) := by
    rcases h12290 with q0 | q1 | q2
    · exact False.elim (q0 u6)
    · exact q1
    · exact False.elim (u3 q2)
  rcases h20699 with q0 | q1
  · exact False.elim (u8 q0)
  · exact False.elim (u9 q1)

theorem step21867 (p102 p139 p140 p258 p283 p288 p1077 p1115 : Prop)
    (h9406 : (¬ p258) ∨ (¬ p288))
    (h21864 : p283 ∨ p288)
    (h1445 : (¬ p102) ∨ (¬ p140) ∨ (¬ p258))
    (h17264 : (¬ p102) ∨ (¬ p139) ∨ (¬ p283) ∨ (¬ p1077) ∨ (¬ p1115))
    (h21822 : p139 ∨ p140) : (¬ p102) ∨ (¬ p1115) ∨ (¬ p258) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p288) := by
    rcases h9406 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u5 : p283 := by
    rcases h21864 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u6 : (¬ p140) := by
    rcases h1445 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (q2 u2)
  have u7 : (¬ p139) := by
    rcases h17264 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u3)
    · exact False.elim (q4 u1)
  rcases h21822 with q0 | q1
  · exact False.elim (u7 q0)
  · exact False.elim (u6 q1)

theorem step21868 (p102 p103 p115 p116 p117 p118 p119 p120 : Prop)
    (h640 : p115 ∨ p116)
    (h641 : p115 ∨ p117)
    (h642 : p115 ∨ p118)
    (h643 : p115 ∨ p119)
    (h644 : p115 ∨ p120)
    (h547 : p102 ∨ p103 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p115 ∨ p103 ∨ p102 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p115) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p103) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p102) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h547 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21869 (p102 p103 p114 p116 p117 p118 p119 p120 : Prop)
    (h635 : p114 ∨ p116)
    (h636 : p114 ∨ p117)
    (h637 : p114 ∨ p118)
    (h638 : p114 ∨ p119)
    (h639 : p114 ∨ p120)
    (h547 : p102 ∨ p103 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p114 ∨ p103 ∨ p102 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p114) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p103) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h547 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21870 (p102 p103 p113 p116 p117 p118 p119 p120 : Prop)
    (h630 : p113 ∨ p116)
    (h631 : p113 ∨ p117)
    (h632 : p113 ∨ p118)
    (h633 : p113 ∨ p119)
    (h634 : p113 ∨ p120)
    (h547 : p102 ∨ p103 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p113 ∨ p103 ∨ p102 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p113) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p103) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h547 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21871 (p102 p103 p112 p116 p117 p118 p119 p120 : Prop)
    (h625 : p112 ∨ p116)
    (h626 : p112 ∨ p117)
    (h627 : p112 ∨ p118)
    (h628 : p112 ∨ p119)
    (h629 : p112 ∨ p120)
    (h547 : p102 ∨ p103 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p112 ∨ p103 ∨ p102 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p112) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p103) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h547 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21872 (p102 p103 p111 p112 p113 p114 p115 p116 p117 p118 p119 p120 : Prop)
    (h522 : p102 ∨ p103 ∨ (¬ p111) ∨ (¬ p112) ∨ (¬ p113) ∨ (¬ p114) ∨ (¬ p115))
    (h620 : p111 ∨ p116)
    (h621 : p111 ∨ p117)
    (h622 : p111 ∨ p118)
    (h623 : p111 ∨ p119)
    (h624 : p111 ∨ p120)
    (h547 : p102 ∨ p103 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : (¬ p112) ∨ (¬ p115) ∨ (¬ p114) ∨ p102 ∨ (¬ p113) ∨ p103 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p112 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p114 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p102) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p113 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p103) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p111) := by
    rcases h522 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u5 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u2)
    · exact False.elim (q6 u1)
  have u7 : p116 := by
    rcases h620 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p117 := by
    rcases h621 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p118 := by
    rcases h622 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p119 := by
    rcases h623 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p120 := by
    rcases h624 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h547 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21873 (p102 p103 p112 p113 p114 p115 : Prop)
    (h21868 : p115 ∨ p103 ∨ p102)
    (h21869 : p114 ∨ p103 ∨ p102)
    (h21870 : p113 ∨ p103 ∨ p102)
    (h21871 : p112 ∨ p103 ∨ p102)
    (h21872 : (¬ p112) ∨ (¬ p115) ∨ (¬ p114) ∨ p102 ∨ (¬ p113) ∨ p103) : p103 ∨ p102 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p103) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p102) := fun hu => hn (Or.inr hu)
  have u2 : p115 := by
    rcases h21868 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p114 := by
    rcases h21869 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p113 := by
    rcases h21870 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p112 := by
    rcases h21871 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21872 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (u0 q5)

theorem step21874 (p633 p636 p647 p648 p649 p650 p651 p652 : Prop)
    (h3736 : p647 ∨ p648)
    (h3737 : p647 ∨ p649)
    (h3738 : p647 ∨ p650)
    (h3739 : p647 ∨ p651)
    (h3740 : p647 ∨ p652)
    (h3653 : p633 ∨ p636 ∨ (¬ p648) ∨ (¬ p649) ∨ (¬ p650) ∨ (¬ p651) ∨ (¬ p652)) : p647 ∨ p636 ∨ p633 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p647) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p636) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p633) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p648 := by
    rcases h3736 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p649 := by
    rcases h3737 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p650 := by
    rcases h3738 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p651 := by
    rcases h3739 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p652 := by
    rcases h3740 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3653 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21875 (p633 p636 p646 p648 p649 p650 p651 p652 : Prop)
    (h3731 : p646 ∨ p648)
    (h3732 : p646 ∨ p649)
    (h3733 : p646 ∨ p650)
    (h3734 : p646 ∨ p651)
    (h3735 : p646 ∨ p652)
    (h3653 : p633 ∨ p636 ∨ (¬ p648) ∨ (¬ p649) ∨ (¬ p650) ∨ (¬ p651) ∨ (¬ p652)) : p646 ∨ p636 ∨ p633 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p646) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p636) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h3653 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21876 (p633 p636 p645 p648 p649 p650 p651 p652 : Prop)
    (h3726 : p645 ∨ p648)
    (h3727 : p645 ∨ p649)
    (h3728 : p645 ∨ p650)
    (h3729 : p645 ∨ p651)
    (h3730 : p645 ∨ p652)
    (h3653 : p633 ∨ p636 ∨ (¬ p648) ∨ (¬ p649) ∨ (¬ p650) ∨ (¬ p651) ∨ (¬ p652)) : p645 ∨ p636 ∨ p633 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p645) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p636) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h3653 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21877 (p633 p636 p644 p648 p649 p650 p651 p652 : Prop)
    (h3721 : p644 ∨ p648)
    (h3722 : p644 ∨ p649)
    (h3723 : p644 ∨ p650)
    (h3724 : p644 ∨ p651)
    (h3725 : p644 ∨ p652)
    (h3653 : p633 ∨ p636 ∨ (¬ p648) ∨ (¬ p649) ∨ (¬ p650) ∨ (¬ p651) ∨ (¬ p652)) : p644 ∨ p636 ∨ p633 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p644) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p636) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h3653 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21878 (p633 p636 p643 p644 p645 p646 p647 p648 p649 p650 p651 p652 : Prop)
    (h3628 : p633 ∨ p636 ∨ (¬ p643) ∨ (¬ p644) ∨ (¬ p645) ∨ (¬ p646) ∨ (¬ p647))
    (h3716 : p643 ∨ p648)
    (h3717 : p643 ∨ p649)
    (h3718 : p643 ∨ p650)
    (h3719 : p643 ∨ p651)
    (h3720 : p643 ∨ p652)
    (h3653 : p633 ∨ p636 ∨ (¬ p648) ∨ (¬ p649) ∨ (¬ p650) ∨ (¬ p651) ∨ (¬ p652)) : (¬ p644) ∨ p636 ∨ (¬ p645) ∨ p633 ∨ (¬ p646) ∨ (¬ p647) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p644 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p636) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p645 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p633) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p646 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p647 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p643) := by
    rcases h3628 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u1 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u2)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u5)
  have u7 : p648 := by
    rcases h3716 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p649 := by
    rcases h3717 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p650 := by
    rcases h3718 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p651 := by
    rcases h3719 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p652 := by
    rcases h3720 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h3653 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21879 (p633 p636 p644 p645 p646 p647 : Prop)
    (h21874 : p647 ∨ p636 ∨ p633)
    (h21875 : p646 ∨ p636 ∨ p633)
    (h21876 : p645 ∨ p636 ∨ p633)
    (h21877 : p644 ∨ p636 ∨ p633)
    (h21878 : (¬ p644) ∨ p636 ∨ (¬ p645) ∨ p633 ∨ (¬ p646) ∨ (¬ p647)) : p636 ∨ p633 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p636) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p633) := fun hu => hn (Or.inr hu)
  have u2 : p647 := by
    rcases h21874 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p646 := by
    rcases h21875 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p645 := by
    rcases h21876 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p644 := by
    rcases h21877 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21878 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u2)

theorem step21880 (p1078 p1082 p1089 p1090 p1091 p1092 p1093 p1094 : Prop)
    (h6470 : p1089 ∨ p1090)
    (h6471 : p1089 ∨ p1091)
    (h6472 : p1089 ∨ p1092)
    (h6473 : p1089 ∨ p1093)
    (h6474 : p1089 ∨ p1094)
    (h6375 : p1078 ∨ p1082 ∨ (¬ p1090) ∨ (¬ p1091) ∨ (¬ p1092) ∨ (¬ p1093) ∨ (¬ p1094)) : p1089 ∨ p1082 ∨ p1078 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1089) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1082) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1078) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1090 := by
    rcases h6470 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1091 := by
    rcases h6471 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1092 := by
    rcases h6472 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1093 := by
    rcases h6473 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1094 := by
    rcases h6474 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6375 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21881 (p1078 p1082 p1088 p1090 p1091 p1092 p1093 p1094 : Prop)
    (h6465 : p1088 ∨ p1090)
    (h6466 : p1088 ∨ p1091)
    (h6467 : p1088 ∨ p1092)
    (h6468 : p1088 ∨ p1093)
    (h6469 : p1088 ∨ p1094)
    (h6375 : p1078 ∨ p1082 ∨ (¬ p1090) ∨ (¬ p1091) ∨ (¬ p1092) ∨ (¬ p1093) ∨ (¬ p1094)) : p1088 ∨ p1082 ∨ p1078 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1088) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1082) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h6375 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21882 (p1078 p1082 p1087 p1090 p1091 p1092 p1093 p1094 : Prop)
    (h6460 : p1087 ∨ p1090)
    (h6461 : p1087 ∨ p1091)
    (h6462 : p1087 ∨ p1092)
    (h6463 : p1087 ∨ p1093)
    (h6464 : p1087 ∨ p1094)
    (h6375 : p1078 ∨ p1082 ∨ (¬ p1090) ∨ (¬ p1091) ∨ (¬ p1092) ∨ (¬ p1093) ∨ (¬ p1094)) : p1087 ∨ p1082 ∨ p1078 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1087) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1082) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h6375 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21883 (p1078 p1082 p1086 p1090 p1091 p1092 p1093 p1094 : Prop)
    (h6455 : p1086 ∨ p1090)
    (h6456 : p1086 ∨ p1091)
    (h6457 : p1086 ∨ p1092)
    (h6458 : p1086 ∨ p1093)
    (h6459 : p1086 ∨ p1094)
    (h6375 : p1078 ∨ p1082 ∨ (¬ p1090) ∨ (¬ p1091) ∨ (¬ p1092) ∨ (¬ p1093) ∨ (¬ p1094)) : p1086 ∨ p1082 ∨ p1078 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1086) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1082) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h6375 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21884 (p1078 p1082 p1085 p1086 p1087 p1088 p1089 p1090 p1091 p1092 p1093 p1094 : Prop)
    (h6350 : p1078 ∨ p1082 ∨ (¬ p1085) ∨ (¬ p1086) ∨ (¬ p1087) ∨ (¬ p1088) ∨ (¬ p1089))
    (h6450 : p1085 ∨ p1090)
    (h6451 : p1085 ∨ p1091)
    (h6452 : p1085 ∨ p1092)
    (h6453 : p1085 ∨ p1093)
    (h6454 : p1085 ∨ p1094)
    (h6375 : p1078 ∨ p1082 ∨ (¬ p1090) ∨ (¬ p1091) ∨ (¬ p1092) ∨ (¬ p1093) ∨ (¬ p1094)) : (¬ p1086) ∨ p1082 ∨ p1078 ∨ (¬ p1087) ∨ (¬ p1089) ∨ (¬ p1088) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1086 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1082) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1078) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1087 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1089 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1088 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1085) := by
    rcases h6350 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u4)
  have u7 : p1090 := by
    rcases h6450 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1091 := by
    rcases h6451 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1092 := by
    rcases h6452 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1093 := by
    rcases h6453 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1094 := by
    rcases h6454 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h6375 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21885 (p1078 p1082 p1086 p1087 p1088 p1089 : Prop)
    (h21880 : p1089 ∨ p1082 ∨ p1078)
    (h21881 : p1088 ∨ p1082 ∨ p1078)
    (h21882 : p1087 ∨ p1082 ∨ p1078)
    (h21883 : p1086 ∨ p1082 ∨ p1078)
    (h21884 : (¬ p1086) ∨ p1082 ∨ p1078 ∨ (¬ p1087) ∨ (¬ p1089) ∨ (¬ p1088)) : p1082 ∨ p1078 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1082) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1078) := fun hu => hn (Or.inr hu)
  have u2 : p1089 := by
    rcases h21880 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1088 := by
    rcases h21881 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1087 := by
    rcases h21882 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1086 := by
    rcases h21883 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21884 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21886 (p101 p121 p285 p1078 p1082 p1115 p1206 : Prop)
    (h21134 : p121 ∨ p1206)
    (h15061 : (¬ p101) ∨ (¬ p1078) ∨ p1206)
    (h18366 : (¬ p101) ∨ (¬ p121) ∨ (¬ p285) ∨ (¬ p1082) ∨ (¬ p1115))
    (h21885 : p1082 ∨ p1078) : p1206 ∨ (¬ p285) ∨ (¬ p101) ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1206) := fun hu => hn (Or.inl hu)
  have u1 : p285 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p121 := by
    rcases h21134 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : (¬ p1078) := by
    rcases h15061 with q0 | q1 | q2
    · exact False.elim (q0 u2)
    · exact q1
    · exact False.elim (u0 q2)
  have u6 : (¬ p1082) := by
    rcases h18366 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u2)
    · exact False.elim (q1 u4)
    · exact False.elim (q2 u1)
    · exact q3
    · exact False.elim (q4 u3)
  rcases h21885 with q0 | q1
  · exact False.elim (u6 q0)
  · exact False.elim (u5 q1)

theorem step21887 (p1096 p1100 p1109 p1110 p1111 p1112 p1113 p1114 : Prop)
    (h6599 : p1109 ∨ p1110)
    (h6600 : p1109 ∨ p1111)
    (h6601 : p1109 ∨ p1112)
    (h6602 : p1109 ∨ p1113)
    (h6603 : p1109 ∨ p1114)
    (h6521 : p1096 ∨ p1100 ∨ (¬ p1110) ∨ (¬ p1111) ∨ (¬ p1112) ∨ (¬ p1113) ∨ (¬ p1114)) : p1109 ∨ p1100 ∨ p1096 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1109) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1100) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1110 := by
    rcases h6599 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1111 := by
    rcases h6600 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1112 := by
    rcases h6601 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1113 := by
    rcases h6602 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1114 := by
    rcases h6603 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6521 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21888 (p1096 p1100 p1108 p1110 p1111 p1112 p1113 p1114 : Prop)
    (h6594 : p1108 ∨ p1110)
    (h6595 : p1108 ∨ p1111)
    (h6596 : p1108 ∨ p1112)
    (h6597 : p1108 ∨ p1113)
    (h6598 : p1108 ∨ p1114)
    (h6521 : p1096 ∨ p1100 ∨ (¬ p1110) ∨ (¬ p1111) ∨ (¬ p1112) ∨ (¬ p1113) ∨ (¬ p1114)) : p1108 ∨ p1100 ∨ p1096 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1108) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1100) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1110 := by
    rcases h6594 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1111 := by
    rcases h6595 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1112 := by
    rcases h6596 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1113 := by
    rcases h6597 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1114 := by
    rcases h6598 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6521 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21889 (p1096 p1100 p1107 p1110 p1111 p1112 p1113 p1114 : Prop)
    (h6589 : p1107 ∨ p1110)
    (h6590 : p1107 ∨ p1111)
    (h6591 : p1107 ∨ p1112)
    (h6592 : p1107 ∨ p1113)
    (h6593 : p1107 ∨ p1114)
    (h6521 : p1096 ∨ p1100 ∨ (¬ p1110) ∨ (¬ p1111) ∨ (¬ p1112) ∨ (¬ p1113) ∨ (¬ p1114)) : p1107 ∨ p1100 ∨ p1096 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1107) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1100) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1110 := by
    rcases h6589 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1111 := by
    rcases h6590 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1112 := by
    rcases h6591 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1113 := by
    rcases h6592 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1114 := by
    rcases h6593 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6521 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21890 (p1096 p1100 p1106 p1110 p1111 p1112 p1113 p1114 : Prop)
    (h6584 : p1106 ∨ p1110)
    (h6585 : p1106 ∨ p1111)
    (h6586 : p1106 ∨ p1112)
    (h6587 : p1106 ∨ p1113)
    (h6588 : p1106 ∨ p1114)
    (h6521 : p1096 ∨ p1100 ∨ (¬ p1110) ∨ (¬ p1111) ∨ (¬ p1112) ∨ (¬ p1113) ∨ (¬ p1114)) : p1106 ∨ p1100 ∨ p1096 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1106) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1100) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1110 := by
    rcases h6584 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1111 := by
    rcases h6585 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1112 := by
    rcases h6586 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1113 := by
    rcases h6587 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1114 := by
    rcases h6588 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6521 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21891 (p1096 p1100 p1105 p1106 p1107 p1108 p1109 p1110 p1111 p1112 p1113 p1114 : Prop)
    (h6496 : p1096 ∨ p1100 ∨ (¬ p1105) ∨ (¬ p1106) ∨ (¬ p1107) ∨ (¬ p1108) ∨ (¬ p1109))
    (h6579 : p1105 ∨ p1110)
    (h6580 : p1105 ∨ p1111)
    (h6581 : p1105 ∨ p1112)
    (h6582 : p1105 ∨ p1113)
    (h6583 : p1105 ∨ p1114)
    (h6521 : p1096 ∨ p1100 ∨ (¬ p1110) ∨ (¬ p1111) ∨ (¬ p1112) ∨ (¬ p1113) ∨ (¬ p1114)) : (¬ p1106) ∨ (¬ p1109) ∨ p1096 ∨ p1100 ∨ (¬ p1107) ∨ (¬ p1108) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1109 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1100) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1107 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1105) := by
    rcases h6496 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p1110 := by
    rcases h6579 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1111 := by
    rcases h6580 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1112 := by
    rcases h6581 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1113 := by
    rcases h6582 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1114 := by
    rcases h6583 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h6521 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21892 (p1096 p1100 p1106 p1107 p1108 p1109 : Prop)
    (h21887 : p1109 ∨ p1100 ∨ p1096)
    (h21888 : p1108 ∨ p1100 ∨ p1096)
    (h21889 : p1107 ∨ p1100 ∨ p1096)
    (h21890 : p1106 ∨ p1100 ∨ p1096)
    (h21891 : (¬ p1106) ∨ (¬ p1109) ∨ p1096 ∨ p1100 ∨ (¬ p1107) ∨ (¬ p1108)) : p1100 ∨ p1096 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1100) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr hu)
  have u2 : p1109 := by
    rcases h21887 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1108 := by
    rcases h21888 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1107 := by
    rcases h21889 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1106 := by
    rcases h21890 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21891 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step21893 (p121 p1207 p1219 p1220 p1221 p1222 p1223 p1224 : Prop)
    (h7318 : p1219 ∨ p1220)
    (h7319 : p1219 ∨ p1221)
    (h7320 : p1219 ∨ p1222)
    (h7321 : p1219 ∨ p1223)
    (h7322 : p1219 ∨ p1224)
    (h7225 : p121 ∨ p1207 ∨ (¬ p1220) ∨ (¬ p1221) ∨ (¬ p1222) ∨ (¬ p1223) ∨ (¬ p1224)) : p1219 ∨ p1207 ∨ p121 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1219) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1207) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p121) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1220 := by
    rcases h7318 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1221 := by
    rcases h7319 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1222 := by
    rcases h7320 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1223 := by
    rcases h7321 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1224 := by
    rcases h7322 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7225 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21894 (p121 p1207 p1218 p1220 p1221 p1222 p1223 p1224 : Prop)
    (h7313 : p1218 ∨ p1220)
    (h7314 : p1218 ∨ p1221)
    (h7315 : p1218 ∨ p1222)
    (h7316 : p1218 ∨ p1223)
    (h7317 : p1218 ∨ p1224)
    (h7225 : p121 ∨ p1207 ∨ (¬ p1220) ∨ (¬ p1221) ∨ (¬ p1222) ∨ (¬ p1223) ∨ (¬ p1224)) : p1218 ∨ p1207 ∨ p121 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1218) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1207) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p121) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1220 := by
    rcases h7313 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1221 := by
    rcases h7314 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1222 := by
    rcases h7315 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1223 := by
    rcases h7316 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1224 := by
    rcases h7317 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7225 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21895 (p121 p1207 p1217 p1220 p1221 p1222 p1223 p1224 : Prop)
    (h7308 : p1217 ∨ p1220)
    (h7309 : p1217 ∨ p1221)
    (h7310 : p1217 ∨ p1222)
    (h7311 : p1217 ∨ p1223)
    (h7312 : p1217 ∨ p1224)
    (h7225 : p121 ∨ p1207 ∨ (¬ p1220) ∨ (¬ p1221) ∨ (¬ p1222) ∨ (¬ p1223) ∨ (¬ p1224)) : p1217 ∨ p1207 ∨ p121 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1217) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1207) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p121) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1220 := by
    rcases h7308 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1221 := by
    rcases h7309 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1222 := by
    rcases h7310 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1223 := by
    rcases h7311 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1224 := by
    rcases h7312 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7225 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21896 (p121 p1207 p1216 p1220 p1221 p1222 p1223 p1224 : Prop)
    (h7303 : p1216 ∨ p1220)
    (h7304 : p1216 ∨ p1221)
    (h7305 : p1216 ∨ p1222)
    (h7306 : p1216 ∨ p1223)
    (h7307 : p1216 ∨ p1224)
    (h7225 : p121 ∨ p1207 ∨ (¬ p1220) ∨ (¬ p1221) ∨ (¬ p1222) ∨ (¬ p1223) ∨ (¬ p1224)) : p1216 ∨ p1207 ∨ p121 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1216) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1207) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p121) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1220 := by
    rcases h7303 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1221 := by
    rcases h7304 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1222 := by
    rcases h7305 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1223 := by
    rcases h7306 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1224 := by
    rcases h7307 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7225 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21897 (p121 p1207 p1215 p1216 p1217 p1218 p1219 p1220 p1221 p1222 p1223 p1224 : Prop)
    (h7200 : p121 ∨ p1207 ∨ (¬ p1215) ∨ (¬ p1216) ∨ (¬ p1217) ∨ (¬ p1218) ∨ (¬ p1219))
    (h7298 : p1215 ∨ p1220)
    (h7299 : p1215 ∨ p1221)
    (h7300 : p1215 ∨ p1222)
    (h7301 : p1215 ∨ p1223)
    (h7302 : p1215 ∨ p1224)
    (h7225 : p121 ∨ p1207 ∨ (¬ p1220) ∨ (¬ p1221) ∨ (¬ p1222) ∨ (¬ p1223) ∨ (¬ p1224)) : (¬ p1216) ∨ (¬ p1217) ∨ p121 ∨ p1207 ∨ (¬ p1218) ∨ (¬ p1219) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1216 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1217 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p121) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1207) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1218 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1219 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1215) := by
    rcases h7200 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u5)
  have u7 : p1220 := by
    rcases h7298 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1221 := by
    rcases h7299 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1222 := by
    rcases h7300 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1223 := by
    rcases h7301 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1224 := by
    rcases h7302 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h7225 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21898 (p121 p1207 p1216 p1217 p1218 p1219 : Prop)
    (h21893 : p1219 ∨ p1207 ∨ p121)
    (h21894 : p1218 ∨ p1207 ∨ p121)
    (h21895 : p1217 ∨ p1207 ∨ p121)
    (h21896 : p1216 ∨ p1207 ∨ p121)
    (h21897 : (¬ p1216) ∨ (¬ p1217) ∨ p121 ∨ p1207 ∨ (¬ p1218) ∨ (¬ p1219)) : p1207 ∨ p121 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1207) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p121) := fun hu => hn (Or.inr hu)
  have u2 : p1219 := by
    rcases h21893 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1218 := by
    rcases h21894 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1217 := by
    rcases h21895 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1216 := by
    rcases h21896 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21897 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u2)

theorem step21899 (p1325 p1335 p1340 p1341 p1342 p1343 p1344 p1345 : Prop)
    (h8092 : p1340 ∨ p1341)
    (h8093 : p1340 ∨ p1342)
    (h8094 : p1340 ∨ p1343)
    (h8095 : p1340 ∨ p1344)
    (h8096 : p1340 ∨ p1345)
    (h8011 : p1325 ∨ p1335 ∨ (¬ p1341) ∨ (¬ p1342) ∨ (¬ p1343) ∨ (¬ p1344) ∨ (¬ p1345)) : p1340 ∨ p1335 ∨ p1325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1340) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1335) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h8011 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21900 (p1325 p1335 p1339 p1341 p1342 p1343 p1344 p1345 : Prop)
    (h8087 : p1339 ∨ p1341)
    (h8088 : p1339 ∨ p1342)
    (h8089 : p1339 ∨ p1343)
    (h8090 : p1339 ∨ p1344)
    (h8091 : p1339 ∨ p1345)
    (h8011 : p1325 ∨ p1335 ∨ (¬ p1341) ∨ (¬ p1342) ∨ (¬ p1343) ∨ (¬ p1344) ∨ (¬ p1345)) : p1339 ∨ p1335 ∨ p1325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1339) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1335) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h8011 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21901 (p1325 p1335 p1338 p1341 p1342 p1343 p1344 p1345 : Prop)
    (h8082 : p1338 ∨ p1341)
    (h8083 : p1338 ∨ p1342)
    (h8084 : p1338 ∨ p1343)
    (h8085 : p1338 ∨ p1344)
    (h8086 : p1338 ∨ p1345)
    (h8011 : p1325 ∨ p1335 ∨ (¬ p1341) ∨ (¬ p1342) ∨ (¬ p1343) ∨ (¬ p1344) ∨ (¬ p1345)) : p1338 ∨ p1335 ∨ p1325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1338) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1335) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h8011 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21902 (p1325 p1335 p1337 p1341 p1342 p1343 p1344 p1345 : Prop)
    (h8077 : p1337 ∨ p1341)
    (h8078 : p1337 ∨ p1342)
    (h8079 : p1337 ∨ p1343)
    (h8080 : p1337 ∨ p1344)
    (h8081 : p1337 ∨ p1345)
    (h8011 : p1325 ∨ p1335 ∨ (¬ p1341) ∨ (¬ p1342) ∨ (¬ p1343) ∨ (¬ p1344) ∨ (¬ p1345)) : p1337 ∨ p1335 ∨ p1325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1337) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1335) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h8011 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21903 (p1325 p1335 p1336 p1337 p1338 p1339 p1340 p1341 p1342 p1343 p1344 p1345 : Prop)
    (h7986 : p1325 ∨ p1335 ∨ (¬ p1336) ∨ (¬ p1337) ∨ (¬ p1338) ∨ (¬ p1339) ∨ (¬ p1340))
    (h8072 : p1336 ∨ p1341)
    (h8073 : p1336 ∨ p1342)
    (h8074 : p1336 ∨ p1343)
    (h8075 : p1336 ∨ p1344)
    (h8076 : p1336 ∨ p1345)
    (h8011 : p1325 ∨ p1335 ∨ (¬ p1341) ∨ (¬ p1342) ∨ (¬ p1343) ∨ (¬ p1344) ∨ (¬ p1345)) : (¬ p1337) ∨ (¬ p1339) ∨ p1325 ∨ (¬ p1338) ∨ (¬ p1340) ∨ p1335 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1337 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1339 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1338 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1340 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1335) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1336) := by
    rcases h7986 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u5 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u1)
    · exact False.elim (q6 u4)
  have u7 : p1341 := by
    rcases h8072 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1342 := by
    rcases h8073 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1343 := by
    rcases h8074 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1344 := by
    rcases h8075 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1345 := by
    rcases h8076 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h8011 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21904 (p1325 p1335 p1337 p1338 p1339 p1340 : Prop)
    (h21899 : p1340 ∨ p1335 ∨ p1325)
    (h21900 : p1339 ∨ p1335 ∨ p1325)
    (h21901 : p1338 ∨ p1335 ∨ p1325)
    (h21902 : p1337 ∨ p1335 ∨ p1325)
    (h21903 : (¬ p1337) ∨ (¬ p1339) ∨ p1325 ∨ (¬ p1338) ∨ (¬ p1340) ∨ p1335) : p1335 ∨ p1325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1335) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr hu)
  have u2 : p1340 := by
    rcases h21899 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1339 := by
    rcases h21900 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1338 := by
    rcases h21901 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1337 := by
    rcases h21902 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21903 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u2)
  · exact False.elim (u0 q5)

theorem step21905 (p435 p1366 p1379 p1380 p1381 p1382 p1383 p1384 : Prop)
    (h8343 : p1379 ∨ p1380)
    (h8344 : p1379 ∨ p1381)
    (h8345 : p1379 ∨ p1382)
    (h8346 : p1379 ∨ p1383)
    (h8347 : p1379 ∨ p1384)
    (h8260 : p435 ∨ p1366 ∨ (¬ p1380) ∨ (¬ p1381) ∨ (¬ p1382) ∨ (¬ p1383) ∨ (¬ p1384)) : p1379 ∨ p1366 ∨ p435 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1379) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1366) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p435) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1380 := by
    rcases h8343 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1381 := by
    rcases h8344 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1382 := by
    rcases h8345 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1383 := by
    rcases h8346 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1384 := by
    rcases h8347 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8260 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21906 (p435 p1366 p1378 p1380 p1381 p1382 p1383 p1384 : Prop)
    (h8338 : p1378 ∨ p1380)
    (h8339 : p1378 ∨ p1381)
    (h8340 : p1378 ∨ p1382)
    (h8341 : p1378 ∨ p1383)
    (h8342 : p1378 ∨ p1384)
    (h8260 : p435 ∨ p1366 ∨ (¬ p1380) ∨ (¬ p1381) ∨ (¬ p1382) ∨ (¬ p1383) ∨ (¬ p1384)) : p1378 ∨ p1366 ∨ p435 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1378) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1366) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p435) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1380 := by
    rcases h8338 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1381 := by
    rcases h8339 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1382 := by
    rcases h8340 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1383 := by
    rcases h8341 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1384 := by
    rcases h8342 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8260 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21907 (p435 p1366 p1377 p1380 p1381 p1382 p1383 p1384 : Prop)
    (h8333 : p1377 ∨ p1380)
    (h8334 : p1377 ∨ p1381)
    (h8335 : p1377 ∨ p1382)
    (h8336 : p1377 ∨ p1383)
    (h8337 : p1377 ∨ p1384)
    (h8260 : p435 ∨ p1366 ∨ (¬ p1380) ∨ (¬ p1381) ∨ (¬ p1382) ∨ (¬ p1383) ∨ (¬ p1384)) : p1377 ∨ p1366 ∨ p435 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1377) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1366) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p435) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1380 := by
    rcases h8333 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1381 := by
    rcases h8334 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1382 := by
    rcases h8335 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1383 := by
    rcases h8336 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1384 := by
    rcases h8337 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8260 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21908 (p435 p1366 p1376 p1380 p1381 p1382 p1383 p1384 : Prop)
    (h8328 : p1376 ∨ p1380)
    (h8329 : p1376 ∨ p1381)
    (h8330 : p1376 ∨ p1382)
    (h8331 : p1376 ∨ p1383)
    (h8332 : p1376 ∨ p1384)
    (h8260 : p435 ∨ p1366 ∨ (¬ p1380) ∨ (¬ p1381) ∨ (¬ p1382) ∨ (¬ p1383) ∨ (¬ p1384)) : p1376 ∨ p1366 ∨ p435 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1376) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1366) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p435) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1380 := by
    rcases h8328 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1381 := by
    rcases h8329 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1382 := by
    rcases h8330 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1383 := by
    rcases h8331 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1384 := by
    rcases h8332 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8260 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21909 (p435 p1366 p1375 p1376 p1377 p1378 p1379 p1380 p1381 p1382 p1383 p1384 : Prop)
    (h8235 : p435 ∨ p1366 ∨ (¬ p1375) ∨ (¬ p1376) ∨ (¬ p1377) ∨ (¬ p1378) ∨ (¬ p1379))
    (h8323 : p1375 ∨ p1380)
    (h8324 : p1375 ∨ p1381)
    (h8325 : p1375 ∨ p1382)
    (h8326 : p1375 ∨ p1383)
    (h8327 : p1375 ∨ p1384)
    (h8260 : p435 ∨ p1366 ∨ (¬ p1380) ∨ (¬ p1381) ∨ (¬ p1382) ∨ (¬ p1383) ∨ (¬ p1384)) : (¬ p1376) ∨ (¬ p1379) ∨ p435 ∨ p1366 ∨ (¬ p1377) ∨ (¬ p1378) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1376 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1379 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p435) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1366) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1377 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1378 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1375) := by
    rcases h8235 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p1380 := by
    rcases h8323 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1381 := by
    rcases h8324 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1382 := by
    rcases h8325 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1383 := by
    rcases h8326 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1384 := by
    rcases h8327 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h8260 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21910 (p435 p1366 p1376 p1377 p1378 p1379 : Prop)
    (h21905 : p1379 ∨ p1366 ∨ p435)
    (h21906 : p1378 ∨ p1366 ∨ p435)
    (h21907 : p1377 ∨ p1366 ∨ p435)
    (h21908 : p1376 ∨ p1366 ∨ p435)
    (h21909 : (¬ p1376) ∨ (¬ p1379) ∨ p435 ∨ p1366 ∨ (¬ p1377) ∨ (¬ p1378)) : p1366 ∨ p435 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1366) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p435) := fun hu => hn (Or.inr hu)
  have u2 : p1379 := by
    rcases h21905 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1378 := by
    rcases h21906 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1377 := by
    rcases h21907 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1376 := by
    rcases h21908 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21909 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step21911 (p10 p301 p303 p323 p329 p384 p386 p387 p434 p438 p996 p1206 p1328 p1334 p1366 : Prop)
    (h15122 : p10 ∨ (¬ p386) ∨ (¬ p1206))
    (h21708 : p303 ∨ p386)
    (h12617 : (¬ p303) ∨ (¬ p387))
    (h21380 : p384 ∨ p387 ∨ p386)
    (h21681 : p323 ∨ p10)
    (h21610 : p329 ∨ p10)
    (h12387 : p996 ∨ (¬ p1328) ∨ (¬ p1366))
    (h18338 : (¬ p301) ∨ (¬ p329) ∨ (¬ p438) ∨ (¬ p1206) ∨ (¬ p1366))
    (h21365 : p1334 ∨ p1328)
    (h21060 : p438 ∨ p434)
    (h17008 : (¬ p323) ∨ (¬ p384) ∨ (¬ p434) ∨ (¬ p1206) ∨ (¬ p1334)) : (¬ p1366) ∨ p996 ∨ (¬ p1206) ∨ (¬ p301) ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p996) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p386) := by
    rcases h15122 with q0 | q1 | q2
    · exact False.elim (u4 q0)
    · exact q1
    · exact False.elim (q2 u2)
  have u6 : p303 := by
    rcases h21708 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u7 : (¬ p387) := by
    rcases h12617 with q0 | q1
    · exact False.elim (q0 u6)
    · exact q1
  have u8 : p384 := by
    rcases h21380 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u7 q1)
    · exact False.elim (u5 q2)
  have u9 : p323 := by
    rcases h21681 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p329 := by
    rcases h21610 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : (¬ p1328) := by
    rcases h12387 with q0 | q1 | q2
    · exact False.elim (u1 q0)
    · exact q1
    · exact False.elim (q2 u0)
  have u12 : (¬ p438) := by
    rcases h18338 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u3)
    · exact False.elim (q1 u10)
    · exact q2
    · exact False.elim (q3 u2)
    · exact False.elim (q4 u0)
  have u13 : p1334 := by
    rcases h21365 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  have u14 : p434 := by
    rcases h21060 with q0 | q1
    · exact False.elim (u12 q0)
    · exact q1
  rcases h17008 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u14)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u13)

theorem step21912 (p1096 p1100 : Prop)
    (h16895 : (¬ p1096) ∨ p1100)
    (h21892 : p1100 ∨ p1096) : p1100 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1100) := fun hu => hn hu
  have u1 : (¬ p1096) := by
    rcases h16895 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h21892 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)

theorem step21913 (p285 p983 p1077 p1117 p1121 p1489 : Prop)
    (h18710 : (¬ p285) ∨ (¬ p983) ∨ (¬ p1077) ∨ (¬ p1117) ∨ (¬ p1489))
    (h9337 : (¬ p983) ∨ (¬ p1121) ∨ (¬ p1489))
    (h21537 : p1121 ∨ p1117) : (¬ p1489) ∨ (¬ p983) ∨ (¬ p1077) ∨ (¬ p285) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p285 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p1117) := by
    rcases h18710 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u3)
    · exact False.elim (q1 u1)
    · exact False.elim (q2 u2)
    · exact q3
    · exact False.elim (q4 u0)
  have u5 : (¬ p1121) := by
    rcases h9337 with q0 | q1 | q2
    · exact False.elim (q0 u1)
    · exact q1
    · exact False.elim (q2 u0)
  rcases h21537 with q0 | q1
  · exact False.elim (u5 q0)
  · exact False.elim (u4 q1)

theorem step21914 (p1116 p1118 p1129 p1130 p1131 p1132 p1133 p1134 : Prop)
    (h6728 : p1129 ∨ p1130)
    (h6729 : p1129 ∨ p1131)
    (h6730 : p1129 ∨ p1132)
    (h6731 : p1129 ∨ p1133)
    (h6732 : p1129 ∨ p1134)
    (h6640 : p1116 ∨ p1118 ∨ (¬ p1130) ∨ (¬ p1131) ∨ (¬ p1132) ∨ (¬ p1133) ∨ (¬ p1134)) : p1129 ∨ p1118 ∨ p1116 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1129) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1118) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1116) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1130 := by
    rcases h6728 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1131 := by
    rcases h6729 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1132 := by
    rcases h6730 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1133 := by
    rcases h6731 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1134 := by
    rcases h6732 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6640 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21915 (p1116 p1118 p1125 p1130 p1131 p1132 p1133 p1134 : Prop)
    (h6708 : p1125 ∨ p1130)
    (h6709 : p1125 ∨ p1131)
    (h6710 : p1125 ∨ p1132)
    (h6711 : p1125 ∨ p1133)
    (h6712 : p1125 ∨ p1134)
    (h6640 : p1116 ∨ p1118 ∨ (¬ p1130) ∨ (¬ p1131) ∨ (¬ p1132) ∨ (¬ p1133) ∨ (¬ p1134)) : p1125 ∨ p1118 ∨ p1116 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1125) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1118) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1116) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h6640 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21916 (p1116 p1118 p1128 p1130 p1131 p1132 p1133 p1134 : Prop)
    (h6723 : p1128 ∨ p1130)
    (h6724 : p1128 ∨ p1131)
    (h6725 : p1128 ∨ p1132)
    (h6726 : p1128 ∨ p1133)
    (h6727 : p1128 ∨ p1134)
    (h6640 : p1116 ∨ p1118 ∨ (¬ p1130) ∨ (¬ p1131) ∨ (¬ p1132) ∨ (¬ p1133) ∨ (¬ p1134)) : p1128 ∨ p1118 ∨ p1116 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1128) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1118) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h6640 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21917 (p1116 p1118 p1127 p1130 p1131 p1132 p1133 p1134 : Prop)
    (h6718 : p1127 ∨ p1130)
    (h6719 : p1127 ∨ p1131)
    (h6720 : p1127 ∨ p1132)
    (h6721 : p1127 ∨ p1133)
    (h6722 : p1127 ∨ p1134)
    (h6640 : p1116 ∨ p1118 ∨ (¬ p1130) ∨ (¬ p1131) ∨ (¬ p1132) ∨ (¬ p1133) ∨ (¬ p1134)) : p1127 ∨ p1118 ∨ p1116 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1127) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1118) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1116) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h6640 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21918 (p1116 p1118 p1122 p1125 p1126 p1127 p1128 p1129 p1130 p1131 p1132 p1133 p1134 : Prop)
    (h21914 : p1129 ∨ p1118 ∨ p1116)
    (h21915 : p1125 ∨ p1118 ∨ p1116)
    (h21916 : p1128 ∨ p1118 ∨ p1116)
    (h21917 : p1127 ∨ p1118 ∨ p1116)
    (h6614 : p1118 ∨ p1122 ∨ (¬ p1125) ∨ (¬ p1126) ∨ (¬ p1127) ∨ (¬ p1128) ∨ (¬ p1129))
    (h6713 : p1126 ∨ p1130)
    (h6714 : p1126 ∨ p1131)
    (h6715 : p1126 ∨ p1132)
    (h6716 : p1126 ∨ p1133)
    (h6717 : p1126 ∨ p1134)
    (h6640 : p1116 ∨ p1118 ∨ (¬ p1130) ∨ (¬ p1131) ∨ (¬ p1132) ∨ (¬ p1133) ∨ (¬ p1134)) : p1118 ∨ p1122 ∨ p1116 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1118) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1122) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1116) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1129 := by
    rcases h21914 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u4 : p1125 := by
    rcases h21915 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u5 : p1128 := by
    rcases h21916 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u6 : p1127 := by
    rcases h21917 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u7 : (¬ p1126) := by
    rcases h6614 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u0 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u4)
    · exact q3
    · exact False.elim (q4 u6)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u3)
  have u8 : p1130 := by
    rcases h6713 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p1131 := by
    rcases h6714 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p1132 := by
    rcases h6715 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p1133 := by
    rcases h6716 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u12 : p1134 := by
    rcases h6717 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h6640 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u12)

theorem step21919 (p102 p104 p111 p112 p113 p114 p115 p116 p117 p118 p119 p120 : Prop)
    (h527 : p102 ∨ p104 ∨ (¬ p111) ∨ (¬ p112) ∨ (¬ p113) ∨ (¬ p114) ∨ (¬ p115))
    (h620 : p111 ∨ p116)
    (h621 : p111 ∨ p117)
    (h622 : p111 ∨ p118)
    (h623 : p111 ∨ p119)
    (h624 : p111 ∨ p120)
    (h552 : p102 ∨ p104 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p104 ∨ (¬ p115) ∨ p102 ∨ (¬ p113) ∨ (¬ p112) ∨ (¬ p114) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p104) := fun hu => hn (Or.inl hu)
  have u1 : p115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p102) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p113 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p112 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p114 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p111) := by
    rcases h527 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u0 q1)
    · exact q2
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p116 := by
    rcases h620 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p117 := by
    rcases h621 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p118 := by
    rcases h622 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p119 := by
    rcases h623 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p120 := by
    rcases h624 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h552 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21920 (p12 p168 p237 p1116 p1118 p1122 p1346 p1349 : Prop)
    (h21177 : p1349 ∨ p1346)
    (h12098 : (¬ p237) ∨ (¬ p1122) ∨ p1346)
    (h18229 : (¬ p12) ∨ (¬ p168) ∨ (¬ p237) ∨ (¬ p1118) ∨ (¬ p1349))
    (h21918 : p1118 ∨ p1122 ∨ p1116) : (¬ p237) ∨ (¬ p168) ∨ p1346 ∨ p1116 ∨ (¬ p12) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p168 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1346) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1116) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1349 := by
    rcases h21177 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : (¬ p1122) := by
    rcases h12098 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (u2 q2)
  have u7 : (¬ p1118) := by
    rcases h18229 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u4)
    · exact False.elim (q1 u1)
    · exact False.elim (q2 u0)
    · exact q3
    · exact False.elim (q4 u5)
  rcases h21918 with q0 | q1 | q2
  · exact False.elim (u7 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (u3 q2)

theorem step21921 (p165 p169 p178 p179 p180 p182 : Prop)
    (h21427 : p182 ∨ p165 ∨ p169)
    (h21428 : p178 ∨ p165 ∨ p169)
    (h21429 : p179 ∨ p165 ∨ p169)
    (h21430 : p180 ∨ p165 ∨ p169)
    (h21674 : p165 ∨ p169 ∨ (¬ p182) ∨ (¬ p178) ∨ (¬ p179) ∨ (¬ p180)) : p165 ∨ p169 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p165) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p169) := fun hu => hn (Or.inr hu)
  have u2 : p182 := by
    rcases h21427 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p178 := by
    rcases h21428 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p179 := by
    rcases h21429 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p180 := by
    rcases h21430 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21674 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)

theorem step21922 (p136 p142 p148 p149 p150 p151 p152 p153 : Prop)
    (h776 : p148 ∨ p149)
    (h777 : p148 ∨ p150)
    (h778 : p148 ∨ p151)
    (h779 : p148 ∨ p152)
    (h780 : p148 ∨ p153)
    (h683 : p136 ∨ p142 ∨ (¬ p149) ∨ (¬ p150) ∨ (¬ p151) ∨ (¬ p152) ∨ (¬ p153)) : p148 ∨ p136 ∨ p142 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p148) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p136) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h683 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21923 (p136 p142 p147 p149 p150 p151 p152 p153 : Prop)
    (h771 : p147 ∨ p149)
    (h772 : p147 ∨ p150)
    (h773 : p147 ∨ p151)
    (h774 : p147 ∨ p152)
    (h775 : p147 ∨ p153)
    (h683 : p136 ∨ p142 ∨ (¬ p149) ∨ (¬ p150) ∨ (¬ p151) ∨ (¬ p152) ∨ (¬ p153)) : p147 ∨ p136 ∨ p142 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p147) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p136) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h683 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21924 (p136 p142 p146 p149 p150 p151 p152 p153 : Prop)
    (h766 : p146 ∨ p149)
    (h767 : p146 ∨ p150)
    (h768 : p146 ∨ p151)
    (h769 : p146 ∨ p152)
    (h770 : p146 ∨ p153)
    (h683 : p136 ∨ p142 ∨ (¬ p149) ∨ (¬ p150) ∨ (¬ p151) ∨ (¬ p152) ∨ (¬ p153)) : p146 ∨ p136 ∨ p142 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p146) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p136) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h683 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21925 (p136 p142 p145 p149 p150 p151 p152 p153 : Prop)
    (h761 : p145 ∨ p149)
    (h762 : p145 ∨ p150)
    (h763 : p145 ∨ p151)
    (h764 : p145 ∨ p152)
    (h765 : p145 ∨ p153)
    (h683 : p136 ∨ p142 ∨ (¬ p149) ∨ (¬ p150) ∨ (¬ p151) ∨ (¬ p152) ∨ (¬ p153)) : p145 ∨ p136 ∨ p142 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p145) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p136) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h683 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21926 (p136 p142 p144 p145 p146 p147 p148 p149 p150 p151 p152 p153 : Prop)
    (h658 : p136 ∨ p142 ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p147) ∨ (¬ p148))
    (h756 : p144 ∨ p149)
    (h757 : p144 ∨ p150)
    (h758 : p144 ∨ p151)
    (h759 : p144 ∨ p152)
    (h760 : p144 ∨ p153)
    (h683 : p136 ∨ p142 ∨ (¬ p149) ∨ (¬ p150) ∨ (¬ p151) ∨ (¬ p152) ∨ (¬ p153)) : (¬ p145) ∨ p136 ∨ p142 ∨ (¬ p146) ∨ (¬ p148) ∨ (¬ p147) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p145 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p136) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p142) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p146 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p148 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p147 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p144) := by
    rcases h658 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u2 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u4)
  have u7 : p149 := by
    rcases h756 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p150 := by
    rcases h757 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p151 := by
    rcases h758 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p152 := by
    rcases h759 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p153 := by
    rcases h760 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h683 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21927 (p136 p142 p145 p146 p147 p148 : Prop)
    (h21922 : p148 ∨ p136 ∨ p142)
    (h21923 : p147 ∨ p136 ∨ p142)
    (h21924 : p146 ∨ p136 ∨ p142)
    (h21925 : p145 ∨ p136 ∨ p142)
    (h21926 : (¬ p145) ∨ p136 ∨ p142 ∨ (¬ p146) ∨ (¬ p148) ∨ (¬ p147)) : p136 ∨ p142 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p136) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p142) := fun hu => hn (Or.inr hu)
  have u2 : p148 := by
    rcases h21922 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p147 := by
    rcases h21923 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p146 := by
    rcases h21924 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p145 := by
    rcases h21925 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21926 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21928 (p63 p87 p91 p96 p97 p98 p99 p100 : Prop)
    (h494 : p91 ∨ p96)
    (h495 : p91 ∨ p97)
    (h496 : p91 ∨ p98)
    (h497 : p91 ∨ p99)
    (h498 : p91 ∨ p100)
    (h441 : p63 ∨ p87 ∨ (¬ p96) ∨ (¬ p97) ∨ (¬ p98) ∨ (¬ p99) ∨ (¬ p100)) : p91 ∨ p87 ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p91) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p87) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p96 := by
    rcases h494 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p97 := by
    rcases h495 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p98 := by
    rcases h496 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p99 := by
    rcases h497 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p100 := by
    rcases h498 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h441 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21929 (p17 p63 p87 p88 p91 p92 p93 p94 p95 p301 p574 p580 p581 p601 : Prop)
    (h14083 : (¬ p301) ∨ (¬ p574) ∨ (¬ p601))
    (h21467 : p581 ∨ p574)
    (h20972 : p574 ∨ p580)
    (h8740 : (¬ p17) ∨ (¬ p88) ∨ (¬ p581))
    (h18781 : (¬ p17) ∨ (¬ p87) ∨ (¬ p301) ∨ (¬ p580) ∨ (¬ p601))
    (h21928 : p91 ∨ p87 ∨ p63)
    (h21841 : p95 ∨ p87 ∨ p63)
    (h21842 : p94 ∨ p87 ∨ p63)
    (h21843 : p93 ∨ p87 ∨ p63)
    (h414 : p87 ∨ p88 ∨ (¬ p91) ∨ (¬ p92) ∨ (¬ p93) ∨ (¬ p94) ∨ (¬ p95))
    (h21844 : p92 ∨ p87 ∨ p63) : (¬ p17) ∨ p63 ∨ (¬ p301) ∨ (¬ p601) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p63) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p574) := by
    rcases h14083 with q0 | q1 | q2
    · exact False.elim (q0 u2)
    · exact q1
    · exact False.elim (q2 u3)
  have u5 : p581 := by
    rcases h21467 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u6 : p580 := by
    rcases h20972 with q0 | q1
    · exact False.elim (u4 q0)
    · exact q1
  have u7 : (¬ p88) := by
    rcases h8740 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (q2 u5)
  have u8 : (¬ p87) := by
    rcases h18781 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (q2 u2)
    · exact False.elim (q3 u6)
    · exact False.elim (q4 u3)
  have u9 : p91 := by
    rcases h21928 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u8 q1)
    · exact False.elim (u1 q2)
  have u10 : p95 := by
    rcases h21841 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u8 q1)
    · exact False.elim (u1 q2)
  have u11 : p94 := by
    rcases h21842 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u8 q1)
    · exact False.elim (u1 q2)
  have u12 : p93 := by
    rcases h21843 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u8 q1)
    · exact False.elim (u1 q2)
  have u13 : (¬ p92) := by
    rcases h414 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u8 q0)
    · exact False.elim (u7 q1)
    · exact False.elim (q2 u9)
    · exact q3
    · exact False.elim (q4 u12)
    · exact False.elim (q5 u11)
    · exact False.elim (q6 u10)
  rcases h21844 with q0 | q1 | q2
  · exact False.elim (u13 q0)
  · exact False.elim (u8 q1)
  · exact False.elim (u1 q2)

theorem step21930 (p102 p104 p115 p116 p117 p118 p119 p120 : Prop)
    (h640 : p115 ∨ p116)
    (h641 : p115 ∨ p117)
    (h642 : p115 ∨ p118)
    (h643 : p115 ∨ p119)
    (h644 : p115 ∨ p120)
    (h552 : p102 ∨ p104 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p115 ∨ p104 ∨ p102 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p115) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p104) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p102) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h552 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21931 (p102 p104 p114 p116 p117 p118 p119 p120 : Prop)
    (h635 : p114 ∨ p116)
    (h636 : p114 ∨ p117)
    (h637 : p114 ∨ p118)
    (h638 : p114 ∨ p119)
    (h639 : p114 ∨ p120)
    (h552 : p102 ∨ p104 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p114 ∨ p104 ∨ p102 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p114) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p104) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h552 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21932 (p102 p104 p113 p116 p117 p118 p119 p120 : Prop)
    (h630 : p113 ∨ p116)
    (h631 : p113 ∨ p117)
    (h632 : p113 ∨ p118)
    (h633 : p113 ∨ p119)
    (h634 : p113 ∨ p120)
    (h552 : p102 ∨ p104 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p113 ∨ p104 ∨ p102 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p113) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p104) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h552 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21933 (p102 p104 p112 p113 p114 p115 p116 p117 p118 p119 p120 : Prop)
    (h21919 : p104 ∨ (¬ p115) ∨ p102 ∨ (¬ p113) ∨ (¬ p112) ∨ (¬ p114))
    (h625 : p112 ∨ p116)
    (h626 : p112 ∨ p117)
    (h627 : p112 ∨ p118)
    (h628 : p112 ∨ p119)
    (h629 : p112 ∨ p120)
    (h552 : p102 ∨ p104 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : (¬ p113) ∨ (¬ p115) ∨ p102 ∨ p104 ∨ (¬ p114) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p113 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p102) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p104) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p114 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p112) := by
    rcases h21919 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (u3 q0)
    · exact False.elim (q1 u1)
    · exact False.elim (u2 q2)
    · exact False.elim (q3 u0)
    · exact q4
    · exact False.elim (q5 u4)
  have u6 : p116 := by
    rcases h625 with q0 | q1
    · exact False.elim (u5 q0)
    · exact q1
  have u7 : p117 := by
    rcases h626 with q0 | q1
    · exact False.elim (u5 q0)
    · exact q1
  have u8 : p118 := by
    rcases h627 with q0 | q1
    · exact False.elim (u5 q0)
    · exact q1
  have u9 : p119 := by
    rcases h628 with q0 | q1
    · exact False.elim (u5 q0)
    · exact q1
  have u10 : p120 := by
    rcases h629 with q0 | q1
    · exact False.elim (u5 q0)
    · exact q1
  rcases h552 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u10)

theorem step21934 (p102 p104 p113 p114 p115 : Prop)
    (h21930 : p115 ∨ p104 ∨ p102)
    (h21931 : p114 ∨ p104 ∨ p102)
    (h21932 : p113 ∨ p104 ∨ p102)
    (h21933 : (¬ p113) ∨ (¬ p115) ∨ p102 ∨ p104 ∨ (¬ p114)) : p104 ∨ p102 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p104) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p102) := fun hu => hn (Or.inr hu)
  have u2 : p115 := by
    rcases h21930 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p114 := by
    rcases h21931 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p113 := by
    rcases h21932 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21933 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u3)

theorem step21936 (p285 p286 p295 p296 p297 p298 p299 p300 : Prop)
    (h1566 : p295 ∨ p296)
    (h1567 : p295 ∨ p297)
    (h1568 : p295 ∨ p298)
    (h1569 : p295 ∨ p299)
    (h1570 : p295 ∨ p300)
    (h1491 : p285 ∨ p286 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300)) : p295 ∨ p285 ∨ p286 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p295) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p285) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p286) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p296 := by
    rcases h1566 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p297 := by
    rcases h1567 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p298 := by
    rcases h1568 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p299 := by
    rcases h1569 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p300 := by
    rcases h1570 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1491 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21937 (p285 p286 p294 p296 p297 p298 p299 p300 : Prop)
    (h1561 : p294 ∨ p296)
    (h1562 : p294 ∨ p297)
    (h1563 : p294 ∨ p298)
    (h1564 : p294 ∨ p299)
    (h1565 : p294 ∨ p300)
    (h1491 : p285 ∨ p286 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300)) : p294 ∨ p285 ∨ p286 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p294) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p285) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p286) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p296 := by
    rcases h1561 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p297 := by
    rcases h1562 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p298 := by
    rcases h1563 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p299 := by
    rcases h1564 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p300 := by
    rcases h1565 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1491 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21938 (p285 p286 p293 p296 p297 p298 p299 p300 : Prop)
    (h1556 : p293 ∨ p296)
    (h1557 : p293 ∨ p297)
    (h1558 : p293 ∨ p298)
    (h1559 : p293 ∨ p299)
    (h1560 : p293 ∨ p300)
    (h1491 : p285 ∨ p286 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300)) : p293 ∨ p285 ∨ p286 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p293) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p285) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p286) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p296 := by
    rcases h1556 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p297 := by
    rcases h1557 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p298 := by
    rcases h1558 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p299 := by
    rcases h1559 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p300 := by
    rcases h1560 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1491 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21939 (p285 p286 p292 p296 p297 p298 p299 p300 : Prop)
    (h1551 : p292 ∨ p296)
    (h1552 : p292 ∨ p297)
    (h1553 : p292 ∨ p298)
    (h1554 : p292 ∨ p299)
    (h1555 : p292 ∨ p300)
    (h1491 : p285 ∨ p286 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300)) : p292 ∨ p285 ∨ p286 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p292) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p285) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p286) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p296 := by
    rcases h1551 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p297 := by
    rcases h1552 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p298 := by
    rcases h1553 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p299 := by
    rcases h1554 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p300 := by
    rcases h1555 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1491 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21940 (p285 p286 p291 p292 p293 p294 p295 p296 p297 p298 p299 p300 : Prop)
    (h1466 : p285 ∨ p286 ∨ (¬ p291) ∨ (¬ p292) ∨ (¬ p293) ∨ (¬ p294) ∨ (¬ p295))
    (h1546 : p291 ∨ p296)
    (h1547 : p291 ∨ p297)
    (h1548 : p291 ∨ p298)
    (h1549 : p291 ∨ p299)
    (h1550 : p291 ∨ p300)
    (h1491 : p285 ∨ p286 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300)) : (¬ p292) ∨ p285 ∨ p286 ∨ (¬ p295) ∨ (¬ p293) ∨ (¬ p294) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p292 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p285) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p286) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p295 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p293 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p294 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p291) := by
    rcases h1466 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u2 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u3)
  have u7 : p296 := by
    rcases h1546 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p297 := by
    rcases h1547 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p298 := by
    rcases h1548 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p299 := by
    rcases h1549 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p300 := by
    rcases h1550 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h1491 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21941 (p285 p286 p292 p293 p294 p295 : Prop)
    (h21936 : p295 ∨ p285 ∨ p286)
    (h21937 : p294 ∨ p285 ∨ p286)
    (h21938 : p293 ∨ p285 ∨ p286)
    (h21939 : p292 ∨ p285 ∨ p286)
    (h21940 : (¬ p292) ∨ p285 ∨ p286 ∨ (¬ p295) ∨ (¬ p293) ∨ (¬ p294)) : p285 ∨ p286 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p285) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p286) := fun hu => hn (Or.inr hu)
  have u2 : p295 := by
    rcases h21936 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p294 := by
    rcases h21937 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p293 := by
    rcases h21938 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p292 := by
    rcases h21939 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21940 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step21942 (p15 p69 p77 p78 p79 p80 p81 p82 : Prop)
    (h389 : p77 ∨ p78)
    (h390 : p77 ∨ p79)
    (h391 : p77 ∨ p80)
    (h392 : p77 ∨ p81)
    (h393 : p77 ∨ p82)
    (h306 : p15 ∨ p69 ∨ (¬ p78) ∨ (¬ p79) ∨ (¬ p80) ∨ (¬ p81) ∨ (¬ p82)) : p77 ∨ p69 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p77) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p69) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h306 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21943 (p15 p69 p76 p78 p79 p80 p81 p82 : Prop)
    (h384 : p76 ∨ p78)
    (h385 : p76 ∨ p79)
    (h386 : p76 ∨ p80)
    (h387 : p76 ∨ p81)
    (h388 : p76 ∨ p82)
    (h306 : p15 ∨ p69 ∨ (¬ p78) ∨ (¬ p79) ∨ (¬ p80) ∨ (¬ p81) ∨ (¬ p82)) : p76 ∨ p69 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p76) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p69) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h306 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21944 (p15 p69 p75 p78 p79 p80 p81 p82 : Prop)
    (h379 : p75 ∨ p78)
    (h380 : p75 ∨ p79)
    (h381 : p75 ∨ p80)
    (h382 : p75 ∨ p81)
    (h383 : p75 ∨ p82)
    (h306 : p15 ∨ p69 ∨ (¬ p78) ∨ (¬ p79) ∨ (¬ p80) ∨ (¬ p81) ∨ (¬ p82)) : p75 ∨ p69 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p75) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p69) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h306 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21945 (p15 p69 p74 p75 p76 p77 p78 p79 p80 p81 p82 : Prop)
    (h21810 : (¬ p74) ∨ (¬ p77) ∨ p69 ∨ p15 ∨ (¬ p75) ∨ (¬ p76))
    (h374 : p74 ∨ p78)
    (h375 : p74 ∨ p79)
    (h376 : p74 ∨ p80)
    (h377 : p74 ∨ p81)
    (h378 : p74 ∨ p82)
    (h306 : p15 ∨ p69 ∨ (¬ p78) ∨ (¬ p79) ∨ (¬ p80) ∨ (¬ p81) ∨ (¬ p82)) : (¬ p75) ∨ (¬ p77) ∨ p69 ∨ p15 ∨ (¬ p76) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p75 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p77 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p69) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p76 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p74) := by
    rcases h21810 with q0 | q1 | q2 | q3 | q4 | q5
    · exact q0
    · exact False.elim (q1 u1)
    · exact False.elim (u2 q2)
    · exact False.elim (u3 q3)
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u4)
  have u6 : p78 := by
    rcases h374 with q0 | q1
    · exact False.elim (u5 q0)
    · exact q1
  have u7 : p79 := by
    rcases h375 with q0 | q1
    · exact False.elim (u5 q0)
    · exact q1
  have u8 : p80 := by
    rcases h376 with q0 | q1
    · exact False.elim (u5 q0)
    · exact q1
  have u9 : p81 := by
    rcases h377 with q0 | q1
    · exact False.elim (u5 q0)
    · exact q1
  have u10 : p82 := by
    rcases h378 with q0 | q1
    · exact False.elim (u5 q0)
    · exact q1
  rcases h306 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u10)

theorem step21946 (p15 p69 p75 p76 p77 : Prop)
    (h21942 : p77 ∨ p69 ∨ p15)
    (h21943 : p76 ∨ p69 ∨ p15)
    (h21944 : p75 ∨ p69 ∨ p15)
    (h21945 : (¬ p75) ∨ (¬ p77) ∨ p69 ∨ p15 ∨ (¬ p76)) : p69 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p69) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr hu)
  have u2 : p77 := by
    rcases h21942 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p76 := by
    rcases h21943 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p75 := by
    rcases h21944 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21945 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u3)

theorem step21948 (p125 p367 p371 p372 p373 p374 p375 p376 p377 p378 p379 p380 : Prop)
    (h20993 : p380 ∨ p125 ∨ p367)
    (h20994 : p371 ∨ p125 ∨ p367)
    (h20995 : p372 ∨ p125 ∨ p367)
    (h20996 : p373 ∨ p125 ∨ p367)
    (h20997 : p374 ∨ p125 ∨ p367)
    (h1964 : p125 ∨ p367 ∨ (¬ p371) ∨ (¬ p372) ∨ (¬ p373) ∨ (¬ p374) ∨ (¬ p375))
    (h2074 : p375 ∨ p376)
    (h2075 : p375 ∨ p377)
    (h2076 : p375 ∨ p378)
    (h2077 : p375 ∨ p379)
    (h1989 : p125 ∨ p367 ∨ (¬ p376) ∨ (¬ p377) ∨ (¬ p378) ∨ (¬ p379) ∨ (¬ p380)) : p367 ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p367) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p125) := fun hu => hn (Or.inr hu)
  have u2 : p380 := by
    rcases h20993 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u3 : p371 := by
    rcases h20994 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u4 : p372 := by
    rcases h20995 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u5 : p373 := by
    rcases h20996 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u6 : p374 := by
    rcases h20997 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u7 : (¬ p375) := by
    rcases h1964 with q0 | q1 | q2 | q3 | q4 | q5 | q6
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
  rcases h1989 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u2)

theorem step21949 (p419 p996 p1009 p1010 p1011 p1012 p1013 p1014 : Prop)
    (h5958 : p1009 ∨ p1010)
    (h5959 : p1009 ∨ p1011)
    (h5960 : p1009 ∨ p1012)
    (h5961 : p1009 ∨ p1013)
    (h5962 : p1009 ∨ p1014)
    (h5875 : p419 ∨ p996 ∨ (¬ p1010) ∨ (¬ p1011) ∨ (¬ p1012) ∨ (¬ p1013) ∨ (¬ p1014)) : p1009 ∨ p419 ∨ p996 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1009) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p419) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p996) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1010 := by
    rcases h5958 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1011 := by
    rcases h5959 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1012 := by
    rcases h5960 with q0 | q1
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
  rcases h5875 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21950 (p419 p996 p1008 p1010 p1011 p1012 p1013 p1014 : Prop)
    (h5953 : p1008 ∨ p1010)
    (h5954 : p1008 ∨ p1011)
    (h5955 : p1008 ∨ p1012)
    (h5956 : p1008 ∨ p1013)
    (h5957 : p1008 ∨ p1014)
    (h5875 : p419 ∨ p996 ∨ (¬ p1010) ∨ (¬ p1011) ∨ (¬ p1012) ∨ (¬ p1013) ∨ (¬ p1014)) : p1008 ∨ p419 ∨ p996 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1008) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p419) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p996) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1010 := by
    rcases h5953 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1011 := by
    rcases h5954 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1012 := by
    rcases h5955 with q0 | q1
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
  rcases h5875 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21951 (p419 p996 p1007 p1010 p1011 p1012 p1013 p1014 : Prop)
    (h5948 : p1007 ∨ p1010)
    (h5949 : p1007 ∨ p1011)
    (h5950 : p1007 ∨ p1012)
    (h5951 : p1007 ∨ p1013)
    (h5952 : p1007 ∨ p1014)
    (h5875 : p419 ∨ p996 ∨ (¬ p1010) ∨ (¬ p1011) ∨ (¬ p1012) ∨ (¬ p1013) ∨ (¬ p1014)) : p1007 ∨ p419 ∨ p996 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1007) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p419) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p996) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1010 := by
    rcases h5948 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1011 := by
    rcases h5949 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1012 := by
    rcases h5950 with q0 | q1
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
  rcases h5875 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21952 (p419 p996 p1006 p1010 p1011 p1012 p1013 p1014 : Prop)
    (h5943 : p1006 ∨ p1010)
    (h5944 : p1006 ∨ p1011)
    (h5945 : p1006 ∨ p1012)
    (h5946 : p1006 ∨ p1013)
    (h5947 : p1006 ∨ p1014)
    (h5875 : p419 ∨ p996 ∨ (¬ p1010) ∨ (¬ p1011) ∨ (¬ p1012) ∨ (¬ p1013) ∨ (¬ p1014)) : p1006 ∨ p419 ∨ p996 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1006) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p419) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p996) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1010 := by
    rcases h5943 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1011 := by
    rcases h5944 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1012 := by
    rcases h5945 with q0 | q1
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
  rcases h5875 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21953 (p419 p996 p1005 p1010 p1011 p1012 p1013 p1014 : Prop)
    (h5938 : p1005 ∨ p1010)
    (h5939 : p1005 ∨ p1011)
    (h5940 : p1005 ∨ p1012)
    (h5941 : p1005 ∨ p1013)
    (h5942 : p1005 ∨ p1014)
    (h5875 : p419 ∨ p996 ∨ (¬ p1010) ∨ (¬ p1011) ∨ (¬ p1012) ∨ (¬ p1013) ∨ (¬ p1014)) : p1005 ∨ p419 ∨ p996 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1005) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p419) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p996) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1010 := by
    rcases h5938 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1011 := by
    rcases h5939 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1012 := by
    rcases h5940 with q0 | q1
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
  rcases h5875 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21954 (p419 p996 p1005 p1006 p1007 p1008 p1009 : Prop)
    (h21949 : p1009 ∨ p419 ∨ p996)
    (h21950 : p1008 ∨ p419 ∨ p996)
    (h21951 : p1007 ∨ p419 ∨ p996)
    (h21952 : p1006 ∨ p419 ∨ p996)
    (h21953 : p1005 ∨ p419 ∨ p996)
    (h5850 : p419 ∨ p996 ∨ (¬ p1005) ∨ (¬ p1006) ∨ (¬ p1007) ∨ (¬ p1008) ∨ (¬ p1009)) : p419 ∨ p996 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p996) := fun hu => hn (Or.inr hu)
  have u2 : p1009 := by
    rcases h21949 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1008 := by
    rcases h21950 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1007 := by
    rcases h21951 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1006 := by
    rcases h21952 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p1005 := by
    rcases h21953 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h5850 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u2)

theorem step21955 (p101 p125 p304 p329 p350 p367 p368 p438 p687 p690 p1366 : Prop)
    (h21374 : p368 ∨ p125)
    (h21948 : p367 ∨ p125)
    (h16999 : (¬ p304) ∨ (¬ p350) ∨ (¬ p368) ∨ (¬ p438) ∨ (¬ p687))
    (h18470 : (¬ p101) ∨ (¬ p329) ∨ (¬ p350) ∨ (¬ p367) ∨ (¬ p690) ∨ (¬ p1366))
    (h20766 : p690 ∨ p687) : p125 ∨ (¬ p438) ∨ (¬ p1366) ∨ (¬ p304) ∨ (¬ p350) ∨ (¬ p101) ∨ (¬ p329) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p125) := fun hu => hn (Or.inl hu)
  have u1 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p329 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p368 := by
    rcases h21374 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p367 := by
    rcases h21948 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : (¬ p687) := by
    rcases h16999 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u3)
    · exact False.elim (q1 u4)
    · exact False.elim (q2 u7)
    · exact False.elim (q3 u1)
    · exact q4
  have u10 : (¬ p690) := by
    rcases h18470 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u5)
    · exact False.elim (q1 u6)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u8)
    · exact q4
    · exact False.elim (q5 u2)
  rcases h20766 with q0 | q1
  · exact False.elim (u10 q0)
  · exact False.elim (u9 q1)

theorem step21956 (p1206 p1212 p1215 p1216 p1217 p1218 p1219 p1220 p1221 p1222 p1223 p1224 : Prop)
    (h7234 : p1206 ∨ p1212 ∨ (¬ p1220) ∨ (¬ p1221) ∨ (¬ p1222) ∨ (¬ p1223) ∨ (¬ p1224))
    (h7301 : p1215 ∨ p1223)
    (h7306 : p1216 ∨ p1223)
    (h7311 : p1217 ∨ p1223)
    (h7316 : p1218 ∨ p1223)
    (h7321 : p1219 ∨ p1223)
    (h7209 : p1206 ∨ p1212 ∨ (¬ p1215) ∨ (¬ p1216) ∨ (¬ p1217) ∨ (¬ p1218) ∨ (¬ p1219)) : (¬ p1221) ∨ (¬ p1222) ∨ p1206 ∨ (¬ p1220) ∨ (¬ p1224) ∨ p1212 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1221 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1222 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1206) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1220 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1212) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1223) := by
    rcases h7234 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u5 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u1)
    · exact q5
    · exact False.elim (q6 u4)
  have u7 : p1215 := by
    rcases h7301 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1216 := by
    rcases h7306 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1217 := by
    rcases h7311 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1218 := by
    rcases h7316 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1219 := by
    rcases h7321 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h7209 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21957 (p1206 p1212 p1220 p1221 p1222 p1224 : Prop)
    (h21483 : p1224 ∨ p1212 ∨ p1206)
    (h21484 : p1220 ∨ p1212 ∨ p1206)
    (h21485 : p1221 ∨ p1212 ∨ p1206)
    (h21486 : p1222 ∨ p1212 ∨ p1206)
    (h21956 : (¬ p1221) ∨ (¬ p1222) ∨ p1206 ∨ (¬ p1220) ∨ (¬ p1224) ∨ p1212) : p1212 ∨ p1206 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1212) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1206) := fun hu => hn (Or.inr hu)
  have u2 : p1224 := by
    rcases h21483 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1220 := by
    rcases h21484 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1221 := by
    rcases h21485 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1222 := by
    rcases h21486 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21956 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)
  · exact False.elim (u0 q5)

theorem step21960 (p185 p241 p249 p250 p251 p252 p253 p254 : Prop)
    (h1300 : p249 ∨ p250)
    (h1301 : p249 ∨ p251)
    (h1302 : p249 ∨ p252)
    (h1303 : p249 ∨ p253)
    (h1304 : p249 ∨ p254)
    (h1215 : p185 ∨ p241 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : p249 ∨ p241 ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p249) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p241) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p250 := by
    rcases h1300 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p251 := by
    rcases h1301 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p252 := by
    rcases h1302 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p253 := by
    rcases h1303 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p254 := by
    rcases h1304 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1215 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21961 (p185 p241 p248 p250 p251 p252 p253 p254 : Prop)
    (h1295 : p248 ∨ p250)
    (h1296 : p248 ∨ p251)
    (h1297 : p248 ∨ p252)
    (h1298 : p248 ∨ p253)
    (h1299 : p248 ∨ p254)
    (h1215 : p185 ∨ p241 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : p248 ∨ p241 ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p248) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p241) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p250 := by
    rcases h1295 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p251 := by
    rcases h1296 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p252 := by
    rcases h1297 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p253 := by
    rcases h1298 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p254 := by
    rcases h1299 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1215 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21962 (p185 p241 p247 p250 p251 p252 p253 p254 : Prop)
    (h1290 : p247 ∨ p250)
    (h1291 : p247 ∨ p251)
    (h1292 : p247 ∨ p252)
    (h1293 : p247 ∨ p253)
    (h1294 : p247 ∨ p254)
    (h1215 : p185 ∨ p241 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : p247 ∨ p241 ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p247) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p241) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p250 := by
    rcases h1290 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p251 := by
    rcases h1291 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p252 := by
    rcases h1292 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p253 := by
    rcases h1293 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p254 := by
    rcases h1294 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1215 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21963 (p185 p241 p246 p250 p251 p252 p253 p254 : Prop)
    (h1285 : p246 ∨ p250)
    (h1286 : p246 ∨ p251)
    (h1287 : p246 ∨ p252)
    (h1288 : p246 ∨ p253)
    (h1289 : p246 ∨ p254)
    (h1215 : p185 ∨ p241 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : p246 ∨ p241 ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p246) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p241) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p250 := by
    rcases h1285 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p251 := by
    rcases h1286 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p252 := by
    rcases h1287 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p253 := by
    rcases h1288 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p254 := by
    rcases h1289 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1215 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21964 (p185 p241 p245 p246 p247 p248 p249 p250 p251 p252 p253 p254 : Prop)
    (h1190 : p185 ∨ p241 ∨ (¬ p245) ∨ (¬ p246) ∨ (¬ p247) ∨ (¬ p248) ∨ (¬ p249))
    (h1280 : p245 ∨ p250)
    (h1281 : p245 ∨ p251)
    (h1282 : p245 ∨ p252)
    (h1283 : p245 ∨ p253)
    (h1284 : p245 ∨ p254)
    (h1215 : p185 ∨ p241 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : (¬ p246) ∨ (¬ p249) ∨ p185 ∨ p241 ∨ (¬ p247) ∨ (¬ p248) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p246 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p241) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p247 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p248 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p245) := by
    rcases h1190 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p250 := by
    rcases h1280 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p251 := by
    rcases h1281 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p252 := by
    rcases h1282 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p253 := by
    rcases h1283 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p254 := by
    rcases h1284 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h1215 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21965 (p185 p241 p246 p247 p248 p249 : Prop)
    (h21960 : p249 ∨ p241 ∨ p185)
    (h21961 : p248 ∨ p241 ∨ p185)
    (h21962 : p247 ∨ p241 ∨ p185)
    (h21963 : p246 ∨ p241 ∨ p185)
    (h21964 : (¬ p246) ∨ (¬ p249) ∨ p185 ∨ p241 ∨ (¬ p247) ∨ (¬ p248)) : p241 ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p241) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr hu)
  have u2 : p249 := by
    rcases h21960 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p248 := by
    rcases h21961 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p247 := by
    rcases h21962 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p246 := by
    rcases h21963 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21964 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step21966 (p458 p462 p469 p470 p471 p472 p473 p474 : Prop)
    (h2595 : p469 ∨ p470)
    (h2596 : p469 ∨ p471)
    (h2597 : p469 ∨ p472)
    (h2598 : p469 ∨ p473)
    (h2599 : p469 ∨ p474)
    (h2506 : p458 ∨ p462 ∨ (¬ p470) ∨ (¬ p471) ∨ (¬ p472) ∨ (¬ p473) ∨ (¬ p474)) : p469 ∨ p462 ∨ p458 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p469) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p462) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p458) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p470 := by
    rcases h2595 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p471 := by
    rcases h2596 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p472 := by
    rcases h2597 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p473 := by
    rcases h2598 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p474 := by
    rcases h2599 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2506 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21967 (p458 p462 p468 p470 p471 p472 p473 p474 : Prop)
    (h2590 : p468 ∨ p470)
    (h2591 : p468 ∨ p471)
    (h2592 : p468 ∨ p472)
    (h2593 : p468 ∨ p473)
    (h2594 : p468 ∨ p474)
    (h2506 : p458 ∨ p462 ∨ (¬ p470) ∨ (¬ p471) ∨ (¬ p472) ∨ (¬ p473) ∨ (¬ p474)) : p468 ∨ p462 ∨ p458 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p468) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p462) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p458) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p470 := by
    rcases h2590 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p471 := by
    rcases h2591 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p472 := by
    rcases h2592 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p473 := by
    rcases h2593 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p474 := by
    rcases h2594 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2506 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21968 (p458 p462 p467 p470 p471 p472 p473 p474 : Prop)
    (h2585 : p467 ∨ p470)
    (h2586 : p467 ∨ p471)
    (h2587 : p467 ∨ p472)
    (h2588 : p467 ∨ p473)
    (h2589 : p467 ∨ p474)
    (h2506 : p458 ∨ p462 ∨ (¬ p470) ∨ (¬ p471) ∨ (¬ p472) ∨ (¬ p473) ∨ (¬ p474)) : p467 ∨ p462 ∨ p458 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p467) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p462) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p458) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p470 := by
    rcases h2585 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p471 := by
    rcases h2586 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p472 := by
    rcases h2587 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p473 := by
    rcases h2588 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p474 := by
    rcases h2589 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2506 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21969 (p458 p462 p466 p470 p471 p472 p473 p474 : Prop)
    (h2580 : p466 ∨ p470)
    (h2581 : p466 ∨ p471)
    (h2582 : p466 ∨ p472)
    (h2583 : p466 ∨ p473)
    (h2584 : p466 ∨ p474)
    (h2506 : p458 ∨ p462 ∨ (¬ p470) ∨ (¬ p471) ∨ (¬ p472) ∨ (¬ p473) ∨ (¬ p474)) : p466 ∨ p462 ∨ p458 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p466) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p462) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p458) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p470 := by
    rcases h2580 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p471 := by
    rcases h2581 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p472 := by
    rcases h2582 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p473 := by
    rcases h2583 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p474 := by
    rcases h2584 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2506 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21970 (p458 p462 p465 p466 p467 p468 p469 p470 p471 p472 p473 p474 : Prop)
    (h2481 : p458 ∨ p462 ∨ (¬ p465) ∨ (¬ p466) ∨ (¬ p467) ∨ (¬ p468) ∨ (¬ p469))
    (h2575 : p465 ∨ p470)
    (h2576 : p465 ∨ p471)
    (h2577 : p465 ∨ p472)
    (h2578 : p465 ∨ p473)
    (h2579 : p465 ∨ p474)
    (h2506 : p458 ∨ p462 ∨ (¬ p470) ∨ (¬ p471) ∨ (¬ p472) ∨ (¬ p473) ∨ (¬ p474)) : (¬ p466) ∨ (¬ p469) ∨ p462 ∨ p458 ∨ (¬ p467) ∨ (¬ p468) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p466 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p469 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p462) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p458) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p467 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p468 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p465) := by
    rcases h2481 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p470 := by
    rcases h2575 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p471 := by
    rcases h2576 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p472 := by
    rcases h2577 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p473 := by
    rcases h2578 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p474 := by
    rcases h2579 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h2506 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21971 (p458 p462 p466 p467 p468 p469 : Prop)
    (h21966 : p469 ∨ p462 ∨ p458)
    (h21967 : p468 ∨ p462 ∨ p458)
    (h21968 : p467 ∨ p462 ∨ p458)
    (h21969 : p466 ∨ p462 ∨ p458)
    (h21970 : (¬ p466) ∨ (¬ p469) ∨ p462 ∨ p458 ∨ (¬ p467) ∨ (¬ p468)) : p462 ∨ p458 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p462) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p458) := fun hu => hn (Or.inr hu)
  have u2 : p469 := by
    rcases h21966 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p468 := by
    rcases h21967 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p467 := by
    rcases h21968 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p466 := by
    rcases h21969 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21970 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step21972 (p458 p462 p532 p636 p1084 p1225 : Prop)
    (h10255 : (¬ p458) ∨ (¬ p532) ∨ (¬ p1225))
    (h17009 : (¬ p462) ∨ (¬ p532) ∨ (¬ p636) ∨ (¬ p1084) ∨ (¬ p1225))
    (h21971 : p462 ∨ p458) : (¬ p1225) ∨ (¬ p532) ∨ (¬ p1084) ∨ (¬ p636) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p458) := by
    rcases h10255 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u1)
    · exact False.elim (q2 u0)
  have u5 : (¬ p462) := by
    rcases h17009 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u2)
    · exact False.elim (q4 u0)
  rcases h21971 with q0 | q1
  · exact False.elim (u5 q0)
  · exact False.elim (u4 q1)

theorem step21978 (p833 p834 p847 p848 p849 p850 p851 p852 : Prop)
    (h4915 : p847 ∨ p848)
    (h4916 : p847 ∨ p849)
    (h4917 : p847 ∨ p850)
    (h4918 : p847 ∨ p851)
    (h4919 : p847 ∨ p852)
    (h4820 : p833 ∨ p834 ∨ (¬ p848) ∨ (¬ p849) ∨ (¬ p850) ∨ (¬ p851) ∨ (¬ p852)) : p847 ∨ p834 ∨ p833 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p847) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p834) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p833) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p848 := by
    rcases h4915 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p849 := by
    rcases h4916 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p850 := by
    rcases h4917 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p851 := by
    rcases h4918 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p852 := by
    rcases h4919 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4820 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21979 (p833 p834 p846 p848 p849 p850 p851 p852 : Prop)
    (h4910 : p846 ∨ p848)
    (h4911 : p846 ∨ p849)
    (h4912 : p846 ∨ p850)
    (h4913 : p846 ∨ p851)
    (h4914 : p846 ∨ p852)
    (h4820 : p833 ∨ p834 ∨ (¬ p848) ∨ (¬ p849) ∨ (¬ p850) ∨ (¬ p851) ∨ (¬ p852)) : p846 ∨ p834 ∨ p833 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p846) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p834) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p833) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p848 := by
    rcases h4910 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p849 := by
    rcases h4911 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p850 := by
    rcases h4912 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p851 := by
    rcases h4913 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p852 := by
    rcases h4914 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4820 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21980 (p833 p834 p845 p848 p849 p850 p851 p852 : Prop)
    (h4905 : p845 ∨ p848)
    (h4906 : p845 ∨ p849)
    (h4907 : p845 ∨ p850)
    (h4908 : p845 ∨ p851)
    (h4909 : p845 ∨ p852)
    (h4820 : p833 ∨ p834 ∨ (¬ p848) ∨ (¬ p849) ∨ (¬ p850) ∨ (¬ p851) ∨ (¬ p852)) : p845 ∨ p834 ∨ p833 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p845) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p834) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p833) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p848 := by
    rcases h4905 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p849 := by
    rcases h4906 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p850 := by
    rcases h4907 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p851 := by
    rcases h4908 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p852 := by
    rcases h4909 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4820 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21981 (p833 p834 p844 p848 p849 p850 p851 p852 : Prop)
    (h4900 : p844 ∨ p848)
    (h4901 : p844 ∨ p849)
    (h4902 : p844 ∨ p850)
    (h4903 : p844 ∨ p851)
    (h4904 : p844 ∨ p852)
    (h4820 : p833 ∨ p834 ∨ (¬ p848) ∨ (¬ p849) ∨ (¬ p850) ∨ (¬ p851) ∨ (¬ p852)) : p844 ∨ p834 ∨ p833 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p844) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p834) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p833) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p848 := by
    rcases h4900 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p849 := by
    rcases h4901 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p850 := by
    rcases h4902 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p851 := by
    rcases h4903 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p852 := by
    rcases h4904 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4820 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21983 (p836 p840 p847 p848 p849 p850 p851 p852 : Prop)
    (h4915 : p847 ∨ p848)
    (h4916 : p847 ∨ p849)
    (h4917 : p847 ∨ p850)
    (h4918 : p847 ∨ p851)
    (h4919 : p847 ∨ p852)
    (h4832 : p836 ∨ p840 ∨ (¬ p848) ∨ (¬ p849) ∨ (¬ p850) ∨ (¬ p851) ∨ (¬ p852)) : p847 ∨ p840 ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p847) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p840) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p848 := by
    rcases h4915 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p849 := by
    rcases h4916 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p850 := by
    rcases h4917 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p851 := by
    rcases h4918 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p852 := by
    rcases h4919 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4832 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21984 (p836 p840 p846 p848 p849 p850 p851 p852 : Prop)
    (h4910 : p846 ∨ p848)
    (h4911 : p846 ∨ p849)
    (h4912 : p846 ∨ p850)
    (h4913 : p846 ∨ p851)
    (h4914 : p846 ∨ p852)
    (h4832 : p836 ∨ p840 ∨ (¬ p848) ∨ (¬ p849) ∨ (¬ p850) ∨ (¬ p851) ∨ (¬ p852)) : p846 ∨ p840 ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p846) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p840) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p848 := by
    rcases h4910 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p849 := by
    rcases h4911 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p850 := by
    rcases h4912 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p851 := by
    rcases h4913 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p852 := by
    rcases h4914 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4832 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21985 (p836 p840 p845 p848 p849 p850 p851 p852 : Prop)
    (h4905 : p845 ∨ p848)
    (h4906 : p845 ∨ p849)
    (h4907 : p845 ∨ p850)
    (h4908 : p845 ∨ p851)
    (h4909 : p845 ∨ p852)
    (h4832 : p836 ∨ p840 ∨ (¬ p848) ∨ (¬ p849) ∨ (¬ p850) ∨ (¬ p851) ∨ (¬ p852)) : p845 ∨ p840 ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p845) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p840) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p848 := by
    rcases h4905 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p849 := by
    rcases h4906 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p850 := by
    rcases h4907 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p851 := by
    rcases h4908 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p852 := by
    rcases h4909 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4832 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21986 (p836 p840 p844 p848 p849 p850 p851 p852 : Prop)
    (h4900 : p844 ∨ p848)
    (h4901 : p844 ∨ p849)
    (h4902 : p844 ∨ p850)
    (h4903 : p844 ∨ p851)
    (h4904 : p844 ∨ p852)
    (h4832 : p836 ∨ p840 ∨ (¬ p848) ∨ (¬ p849) ∨ (¬ p850) ∨ (¬ p851) ∨ (¬ p852)) : p844 ∨ p840 ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p844) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p840) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p848 := by
    rcases h4900 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p849 := by
    rcases h4901 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p850 := by
    rcases h4902 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p851 := by
    rcases h4903 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p852 := by
    rcases h4904 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4832 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21987 (p836 p840 p843 p844 p845 p846 p847 p848 p849 p850 p851 p852 : Prop)
    (h4807 : p836 ∨ p840 ∨ (¬ p843) ∨ (¬ p844) ∨ (¬ p845) ∨ (¬ p846) ∨ (¬ p847))
    (h4895 : p843 ∨ p848)
    (h4896 : p843 ∨ p849)
    (h4897 : p843 ∨ p850)
    (h4898 : p843 ∨ p851)
    (h4899 : p843 ∨ p852)
    (h4832 : p836 ∨ p840 ∨ (¬ p848) ∨ (¬ p849) ∨ (¬ p850) ∨ (¬ p851) ∨ (¬ p852)) : (¬ p844) ∨ (¬ p847) ∨ p840 ∨ p836 ∨ (¬ p845) ∨ (¬ p846) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p844 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p847 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p840) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p845 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p846 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p843) := by
    rcases h4807 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p848 := by
    rcases h4895 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p849 := by
    rcases h4896 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p850 := by
    rcases h4897 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p851 := by
    rcases h4898 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p852 := by
    rcases h4899 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h4832 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21988 (p836 p840 p844 p845 p846 p847 : Prop)
    (h21983 : p847 ∨ p840 ∨ p836)
    (h21984 : p846 ∨ p840 ∨ p836)
    (h21985 : p845 ∨ p840 ∨ p836)
    (h21986 : p844 ∨ p840 ∨ p836)
    (h21987 : (¬ p844) ∨ (¬ p847) ∨ p840 ∨ p836 ∨ (¬ p845) ∨ (¬ p846)) : p840 ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p840) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p836) := fun hu => hn (Or.inr hu)
  have u2 : p847 := by
    rcases h21983 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p846 := by
    rcases h21984 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p845 := by
    rcases h21985 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p844 := by
    rcases h21986 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21987 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step21989 (p419 p1004 p1009 p1010 p1011 p1012 p1013 p1014 : Prop)
    (h5958 : p1009 ∨ p1010)
    (h5959 : p1009 ∨ p1011)
    (h5960 : p1009 ∨ p1012)
    (h5961 : p1009 ∨ p1013)
    (h5962 : p1009 ∨ p1014)
    (h5877 : p419 ∨ p1004 ∨ (¬ p1010) ∨ (¬ p1011) ∨ (¬ p1012) ∨ (¬ p1013) ∨ (¬ p1014)) : p1009 ∨ p1004 ∨ p419 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1009) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1004) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p419) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1010 := by
    rcases h5958 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1011 := by
    rcases h5959 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1012 := by
    rcases h5960 with q0 | q1
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
  rcases h5877 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21990 (p419 p1004 p1008 p1010 p1011 p1012 p1013 p1014 : Prop)
    (h5953 : p1008 ∨ p1010)
    (h5954 : p1008 ∨ p1011)
    (h5955 : p1008 ∨ p1012)
    (h5956 : p1008 ∨ p1013)
    (h5957 : p1008 ∨ p1014)
    (h5877 : p419 ∨ p1004 ∨ (¬ p1010) ∨ (¬ p1011) ∨ (¬ p1012) ∨ (¬ p1013) ∨ (¬ p1014)) : p1008 ∨ p1004 ∨ p419 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1008) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1004) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p419) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1010 := by
    rcases h5953 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1011 := by
    rcases h5954 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1012 := by
    rcases h5955 with q0 | q1
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
  rcases h5877 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21991 (p419 p1004 p1007 p1010 p1011 p1012 p1013 p1014 : Prop)
    (h5948 : p1007 ∨ p1010)
    (h5949 : p1007 ∨ p1011)
    (h5950 : p1007 ∨ p1012)
    (h5951 : p1007 ∨ p1013)
    (h5952 : p1007 ∨ p1014)
    (h5877 : p419 ∨ p1004 ∨ (¬ p1010) ∨ (¬ p1011) ∨ (¬ p1012) ∨ (¬ p1013) ∨ (¬ p1014)) : p1007 ∨ p1004 ∨ p419 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1007) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1004) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p419) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1010 := by
    rcases h5948 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1011 := by
    rcases h5949 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1012 := by
    rcases h5950 with q0 | q1
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
  rcases h5877 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21992 (p419 p1004 p1006 p1010 p1011 p1012 p1013 p1014 : Prop)
    (h5943 : p1006 ∨ p1010)
    (h5944 : p1006 ∨ p1011)
    (h5945 : p1006 ∨ p1012)
    (h5946 : p1006 ∨ p1013)
    (h5947 : p1006 ∨ p1014)
    (h5877 : p419 ∨ p1004 ∨ (¬ p1010) ∨ (¬ p1011) ∨ (¬ p1012) ∨ (¬ p1013) ∨ (¬ p1014)) : p1006 ∨ p1004 ∨ p419 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1006) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1004) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p419) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1010 := by
    rcases h5943 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1011 := by
    rcases h5944 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1012 := by
    rcases h5945 with q0 | q1
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
  rcases h5877 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21993 (p419 p1004 p1005 p1006 p1007 p1008 p1009 p1010 p1011 p1012 p1013 p1014 : Prop)
    (h5852 : p419 ∨ p1004 ∨ (¬ p1005) ∨ (¬ p1006) ∨ (¬ p1007) ∨ (¬ p1008) ∨ (¬ p1009))
    (h5938 : p1005 ∨ p1010)
    (h5939 : p1005 ∨ p1011)
    (h5940 : p1005 ∨ p1012)
    (h5941 : p1005 ∨ p1013)
    (h5942 : p1005 ∨ p1014)
    (h5877 : p419 ∨ p1004 ∨ (¬ p1010) ∨ (¬ p1011) ∨ (¬ p1012) ∨ (¬ p1013) ∨ (¬ p1014)) : (¬ p1006) ∨ (¬ p1009) ∨ p419 ∨ p1004 ∨ (¬ p1007) ∨ (¬ p1008) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1006 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1009 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1004) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1007 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1008 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1005) := by
    rcases h5852 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p1010 := by
    rcases h5938 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1011 := by
    rcases h5939 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1012 := by
    rcases h5940 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1013 := by
    rcases h5941 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1014 := by
    rcases h5942 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h5877 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21994 (p419 p1004 p1006 p1007 p1008 p1009 : Prop)
    (h21989 : p1009 ∨ p1004 ∨ p419)
    (h21990 : p1008 ∨ p1004 ∨ p419)
    (h21991 : p1007 ∨ p1004 ∨ p419)
    (h21992 : p1006 ∨ p1004 ∨ p419)
    (h21993 : (¬ p1006) ∨ (¬ p1009) ∨ p419 ∨ p1004 ∨ (¬ p1007) ∨ (¬ p1008)) : p1004 ∨ p419 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1004) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p419) := fun hu => hn (Or.inr hu)
  have u2 : p1009 := by
    rcases h21989 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1008 := by
    rcases h21990 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1007 := by
    rcases h21991 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1006 := by
    rcases h21992 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21993 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step21997 (p156 p163 p173 p174 p175 p176 p177 p181 : Prop)
    (h893 : p173 ∨ p181)
    (h898 : p174 ∨ p181)
    (h903 : p175 ∨ p181)
    (h908 : p176 ∨ p181)
    (h913 : p177 ∨ p181)
    (h807 : p156 ∨ p163 ∨ (¬ p173) ∨ (¬ p174) ∨ (¬ p175) ∨ (¬ p176) ∨ (¬ p177)) : p181 ∨ p156 ∨ p163 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p181) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p156) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p163) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p173 := by
    rcases h893 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p174 := by
    rcases h898 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p175 := by
    rcases h903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p176 := by
    rcases h908 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p177 := by
    rcases h913 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h807 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21998 (p156 p163 p173 p174 p175 p176 p177 p182 : Prop)
    (h894 : p173 ∨ p182)
    (h899 : p174 ∨ p182)
    (h904 : p175 ∨ p182)
    (h909 : p176 ∨ p182)
    (h914 : p177 ∨ p182)
    (h807 : p156 ∨ p163 ∨ (¬ p173) ∨ (¬ p174) ∨ (¬ p175) ∨ (¬ p176) ∨ (¬ p177)) : p182 ∨ p156 ∨ p163 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p182) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p156) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p163) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h807 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21999 (p156 p163 p173 p174 p175 p176 p177 p180 : Prop)
    (h892 : p173 ∨ p180)
    (h897 : p174 ∨ p180)
    (h902 : p175 ∨ p180)
    (h907 : p176 ∨ p180)
    (h912 : p177 ∨ p180)
    (h807 : p156 ∨ p163 ∨ (¬ p173) ∨ (¬ p174) ∨ (¬ p175) ∨ (¬ p176) ∨ (¬ p177)) : p180 ∨ p156 ∨ p163 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p180) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p156) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p163) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h807 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22000 (p156 p163 p173 p174 p175 p176 p177 p179 : Prop)
    (h891 : p173 ∨ p179)
    (h896 : p174 ∨ p179)
    (h901 : p175 ∨ p179)
    (h906 : p176 ∨ p179)
    (h911 : p177 ∨ p179)
    (h807 : p156 ∨ p163 ∨ (¬ p173) ∨ (¬ p174) ∨ (¬ p175) ∨ (¬ p176) ∨ (¬ p177)) : p179 ∨ p156 ∨ p163 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p179) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p156) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p163) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h807 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22001 (p156 p163 p170 p173 p174 p175 p176 p177 p178 p179 p180 p181 p182 : Prop)
    (h21997 : p181 ∨ p156 ∨ p163)
    (h21998 : p182 ∨ p156 ∨ p163)
    (h21999 : p180 ∨ p156 ∨ p163)
    (h22000 : p179 ∨ p156 ∨ p163)
    (h831 : p156 ∨ p170 ∨ (¬ p178) ∨ (¬ p179) ∨ (¬ p180) ∨ (¬ p181) ∨ (¬ p182))
    (h890 : p173 ∨ p178)
    (h895 : p174 ∨ p178)
    (h900 : p175 ∨ p178)
    (h905 : p176 ∨ p178)
    (h910 : p177 ∨ p178)
    (h807 : p156 ∨ p163 ∨ (¬ p173) ∨ (¬ p174) ∨ (¬ p175) ∨ (¬ p176) ∨ (¬ p177)) : p156 ∨ p170 ∨ p163 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p156) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p170) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p163) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p181 := by
    rcases h21997 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u4 : p182 := by
    rcases h21998 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u5 : p180 := by
    rcases h21999 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u6 : p179 := by
    rcases h22000 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u7 : (¬ p178) := by
    rcases h831 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u0 q0)
    · exact False.elim (u1 q1)
    · exact q2
    · exact False.elim (q3 u6)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u3)
    · exact False.elim (q6 u4)
  have u8 : p173 := by
    rcases h890 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p174 := by
    rcases h895 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p175 := by
    rcases h900 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p176 := by
    rcases h905 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u12 : p177 := by
    rcases h910 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h807 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u12)

theorem step22002 (p238 p241 p245 p250 p251 p252 p253 p254 : Prop)
    (h1280 : p245 ∨ p250)
    (h1281 : p245 ∨ p251)
    (h1282 : p245 ∨ p252)
    (h1283 : p245 ∨ p253)
    (h1284 : p245 ∨ p254)
    (h1205 : p238 ∨ p241 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : p245 ∨ p238 ∨ p241 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p245) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p238) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p241) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p250 := by
    rcases h1280 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p251 := by
    rcases h1281 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p252 := by
    rcases h1282 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p253 := by
    rcases h1283 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p254 := by
    rcases h1284 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1205 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22003 (p238 p241 p249 p250 p251 p252 p253 p254 : Prop)
    (h1300 : p249 ∨ p250)
    (h1301 : p249 ∨ p251)
    (h1302 : p249 ∨ p252)
    (h1303 : p249 ∨ p253)
    (h1304 : p249 ∨ p254)
    (h1205 : p238 ∨ p241 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : p249 ∨ p238 ∨ p241 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p249) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p238) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p241) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p250 := by
    rcases h1300 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p251 := by
    rcases h1301 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p252 := by
    rcases h1302 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p253 := by
    rcases h1303 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p254 := by
    rcases h1304 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1205 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22004 (p238 p241 p248 p250 p251 p252 p253 p254 : Prop)
    (h1295 : p248 ∨ p250)
    (h1296 : p248 ∨ p251)
    (h1297 : p248 ∨ p252)
    (h1298 : p248 ∨ p253)
    (h1299 : p248 ∨ p254)
    (h1205 : p238 ∨ p241 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : p248 ∨ p238 ∨ p241 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p248) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p238) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p241) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p250 := by
    rcases h1295 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p251 := by
    rcases h1296 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p252 := by
    rcases h1297 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p253 := by
    rcases h1298 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p254 := by
    rcases h1299 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1205 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22005 (p238 p241 p247 p250 p251 p252 p253 p254 : Prop)
    (h1290 : p247 ∨ p250)
    (h1291 : p247 ∨ p251)
    (h1292 : p247 ∨ p252)
    (h1293 : p247 ∨ p253)
    (h1294 : p247 ∨ p254)
    (h1205 : p238 ∨ p241 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : p247 ∨ p238 ∨ p241 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p247) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p238) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p241) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p250 := by
    rcases h1290 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p251 := by
    rcases h1291 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p252 := by
    rcases h1292 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p253 := by
    rcases h1293 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p254 := by
    rcases h1294 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1205 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22006 (p238 p241 p245 p246 p247 p248 p249 p250 p251 p252 p253 p254 : Prop)
    (h1180 : p238 ∨ p241 ∨ (¬ p245) ∨ (¬ p246) ∨ (¬ p247) ∨ (¬ p248) ∨ (¬ p249))
    (h1285 : p246 ∨ p250)
    (h1286 : p246 ∨ p251)
    (h1287 : p246 ∨ p252)
    (h1288 : p246 ∨ p253)
    (h1289 : p246 ∨ p254)
    (h1205 : p238 ∨ p241 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : (¬ p247) ∨ (¬ p249) ∨ p241 ∨ p238 ∨ (¬ p248) ∨ (¬ p245) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p247 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p241) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p238) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p248 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p245 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p246) := by
    rcases h1180 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u5)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u1)
  have u7 : p250 := by
    rcases h1285 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p251 := by
    rcases h1286 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p252 := by
    rcases h1287 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p253 := by
    rcases h1288 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p254 := by
    rcases h1289 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h1205 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22007 (p238 p241 p245 p247 p248 p249 : Prop)
    (h22002 : p245 ∨ p238 ∨ p241)
    (h22003 : p249 ∨ p238 ∨ p241)
    (h22004 : p248 ∨ p238 ∨ p241)
    (h22005 : p247 ∨ p238 ∨ p241)
    (h22006 : (¬ p247) ∨ (¬ p249) ∨ p241 ∨ p238 ∨ (¬ p248) ∨ (¬ p245)) : p238 ∨ p241 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p238) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p241) := fun hu => hn (Or.inr hu)
  have u2 : p245 := by
    rcases h22002 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p249 := by
    rcases h22003 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p248 := by
    rcases h22004 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p247 := by
    rcases h22005 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22006 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u2)

theorem step22009 (p237 p238 p246 p250 p251 p252 p253 p254 : Prop)
    (h1285 : p246 ∨ p250)
    (h1286 : p246 ∨ p251)
    (h1287 : p246 ∨ p252)
    (h1288 : p246 ∨ p253)
    (h1289 : p246 ∨ p254)
    (h1207 : p237 ∨ p238 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : p246 ∨ p238 ∨ p237 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p246) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p238) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p237) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p250 := by
    rcases h1285 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p251 := by
    rcases h1286 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p252 := by
    rcases h1287 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p253 := by
    rcases h1288 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p254 := by
    rcases h1289 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1207 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22010 (p237 p238 p245 p250 p251 p252 p253 p254 : Prop)
    (h1280 : p245 ∨ p250)
    (h1281 : p245 ∨ p251)
    (h1282 : p245 ∨ p252)
    (h1283 : p245 ∨ p253)
    (h1284 : p245 ∨ p254)
    (h1207 : p237 ∨ p238 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : p245 ∨ p238 ∨ p237 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p245) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p238) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p237) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p250 := by
    rcases h1280 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p251 := by
    rcases h1281 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p252 := by
    rcases h1282 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p253 := by
    rcases h1283 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p254 := by
    rcases h1284 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1207 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22011 (p237 p238 p249 p250 p251 p252 p253 p254 : Prop)
    (h1300 : p249 ∨ p250)
    (h1301 : p249 ∨ p251)
    (h1302 : p249 ∨ p252)
    (h1303 : p249 ∨ p253)
    (h1304 : p249 ∨ p254)
    (h1207 : p237 ∨ p238 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : p249 ∨ p238 ∨ p237 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p249) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p238) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p237) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p250 := by
    rcases h1300 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p251 := by
    rcases h1301 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p252 := by
    rcases h1302 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p253 := by
    rcases h1303 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p254 := by
    rcases h1304 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1207 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22012 (p237 p238 p248 p250 p251 p252 p253 p254 : Prop)
    (h1295 : p248 ∨ p250)
    (h1296 : p248 ∨ p251)
    (h1297 : p248 ∨ p252)
    (h1298 : p248 ∨ p253)
    (h1299 : p248 ∨ p254)
    (h1207 : p237 ∨ p238 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : p248 ∨ p238 ∨ p237 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p248) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p238) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p237) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p250 := by
    rcases h1295 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p251 := by
    rcases h1296 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p252 := by
    rcases h1297 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p253 := by
    rcases h1298 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p254 := by
    rcases h1299 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1207 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22013 (p237 p238 p245 p246 p247 p248 p249 p250 p251 p252 p253 p254 : Prop)
    (h1182 : p237 ∨ p238 ∨ (¬ p245) ∨ (¬ p246) ∨ (¬ p247) ∨ (¬ p248) ∨ (¬ p249))
    (h1290 : p247 ∨ p250)
    (h1291 : p247 ∨ p251)
    (h1292 : p247 ∨ p252)
    (h1293 : p247 ∨ p253)
    (h1294 : p247 ∨ p254)
    (h1207 : p237 ∨ p238 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : (¬ p248) ∨ (¬ p246) ∨ p237 ∨ (¬ p249) ∨ p238 ∨ (¬ p245) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p248 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p246 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p237) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p238) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p245 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p247) := by
    rcases h1182 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u4 q1)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u1)
    · exact q4
    · exact False.elim (q5 u0)
    · exact False.elim (q6 u3)
  have u7 : p250 := by
    rcases h1290 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p251 := by
    rcases h1291 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p252 := by
    rcases h1292 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p253 := by
    rcases h1293 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p254 := by
    rcases h1294 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h1207 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22014 (p237 p238 p245 p246 p248 p249 : Prop)
    (h22009 : p246 ∨ p238 ∨ p237)
    (h22010 : p245 ∨ p238 ∨ p237)
    (h22011 : p249 ∨ p238 ∨ p237)
    (h22012 : p248 ∨ p238 ∨ p237)
    (h22013 : (¬ p248) ∨ (¬ p246) ∨ p237 ∨ (¬ p249) ∨ p238 ∨ (¬ p245)) : p238 ∨ p237 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p238) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p237) := fun hu => hn (Or.inr hu)
  have u2 : p246 := by
    rcases h22009 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p245 := by
    rcases h22010 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p249 := by
    rcases h22011 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p248 := by
    rcases h22012 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22013 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (u0 q4)
  · exact False.elim (q5 u3)

theorem step22015 (p923 p928 p934 p935 p936 p937 p938 p939 : Prop)
    (h5453 : p934 ∨ p935)
    (h5454 : p934 ∨ p936)
    (h5455 : p934 ∨ p937)
    (h5456 : p934 ∨ p938)
    (h5457 : p934 ∨ p939)
    (h5365 : p923 ∨ p928 ∨ (¬ p935) ∨ (¬ p936) ∨ (¬ p937) ∨ (¬ p938) ∨ (¬ p939)) : p934 ∨ p923 ∨ p928 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p934) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p923) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p928) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p935 := by
    rcases h5453 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p936 := by
    rcases h5454 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p937 := by
    rcases h5455 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p938 := by
    rcases h5456 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p939 := by
    rcases h5457 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5365 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22016 (p923 p928 p933 p935 p936 p937 p938 p939 : Prop)
    (h5448 : p933 ∨ p935)
    (h5449 : p933 ∨ p936)
    (h5450 : p933 ∨ p937)
    (h5451 : p933 ∨ p938)
    (h5452 : p933 ∨ p939)
    (h5365 : p923 ∨ p928 ∨ (¬ p935) ∨ (¬ p936) ∨ (¬ p937) ∨ (¬ p938) ∨ (¬ p939)) : p933 ∨ p923 ∨ p928 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p933) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p923) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p928) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p935 := by
    rcases h5448 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p936 := by
    rcases h5449 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p937 := by
    rcases h5450 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p938 := by
    rcases h5451 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p939 := by
    rcases h5452 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5365 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22017 (p923 p928 p932 p935 p936 p937 p938 p939 : Prop)
    (h5443 : p932 ∨ p935)
    (h5444 : p932 ∨ p936)
    (h5445 : p932 ∨ p937)
    (h5446 : p932 ∨ p938)
    (h5447 : p932 ∨ p939)
    (h5365 : p923 ∨ p928 ∨ (¬ p935) ∨ (¬ p936) ∨ (¬ p937) ∨ (¬ p938) ∨ (¬ p939)) : p932 ∨ p923 ∨ p928 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p932) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p923) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p928) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p935 := by
    rcases h5443 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p936 := by
    rcases h5444 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p937 := by
    rcases h5445 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p938 := by
    rcases h5446 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p939 := by
    rcases h5447 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5365 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22018 (p923 p928 p931 p935 p936 p937 p938 p939 : Prop)
    (h5438 : p931 ∨ p935)
    (h5439 : p931 ∨ p936)
    (h5440 : p931 ∨ p937)
    (h5441 : p931 ∨ p938)
    (h5442 : p931 ∨ p939)
    (h5365 : p923 ∨ p928 ∨ (¬ p935) ∨ (¬ p936) ∨ (¬ p937) ∨ (¬ p938) ∨ (¬ p939)) : p931 ∨ p923 ∨ p928 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p931) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p923) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p928) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p935 := by
    rcases h5438 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p936 := by
    rcases h5439 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p937 := by
    rcases h5440 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p938 := by
    rcases h5441 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p939 := by
    rcases h5442 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5365 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22020 (p918 p928 p934 p935 p936 p937 p938 p939 : Prop)
    (h5453 : p934 ∨ p935)
    (h5454 : p934 ∨ p936)
    (h5455 : p934 ∨ p937)
    (h5456 : p934 ∨ p938)
    (h5457 : p934 ∨ p939)
    (h5370 : p918 ∨ p928 ∨ (¬ p935) ∨ (¬ p936) ∨ (¬ p937) ∨ (¬ p938) ∨ (¬ p939)) : p934 ∨ p918 ∨ p928 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p934) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p928) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p935 := by
    rcases h5453 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p936 := by
    rcases h5454 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p937 := by
    rcases h5455 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p938 := by
    rcases h5456 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p939 := by
    rcases h5457 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5370 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22021 (p918 p928 p933 p935 p936 p937 p938 p939 : Prop)
    (h5448 : p933 ∨ p935)
    (h5449 : p933 ∨ p936)
    (h5450 : p933 ∨ p937)
    (h5451 : p933 ∨ p938)
    (h5452 : p933 ∨ p939)
    (h5370 : p918 ∨ p928 ∨ (¬ p935) ∨ (¬ p936) ∨ (¬ p937) ∨ (¬ p938) ∨ (¬ p939)) : p933 ∨ p918 ∨ p928 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p933) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p928) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p935 := by
    rcases h5448 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p936 := by
    rcases h5449 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p937 := by
    rcases h5450 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p938 := by
    rcases h5451 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p939 := by
    rcases h5452 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5370 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22022 (p918 p928 p932 p935 p936 p937 p938 p939 : Prop)
    (h5443 : p932 ∨ p935)
    (h5444 : p932 ∨ p936)
    (h5445 : p932 ∨ p937)
    (h5446 : p932 ∨ p938)
    (h5447 : p932 ∨ p939)
    (h5370 : p918 ∨ p928 ∨ (¬ p935) ∨ (¬ p936) ∨ (¬ p937) ∨ (¬ p938) ∨ (¬ p939)) : p932 ∨ p918 ∨ p928 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p932) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p928) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p935 := by
    rcases h5443 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p936 := by
    rcases h5444 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p937 := by
    rcases h5445 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p938 := by
    rcases h5446 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p939 := by
    rcases h5447 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5370 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22023 (p918 p928 p931 p935 p936 p937 p938 p939 : Prop)
    (h5438 : p931 ∨ p935)
    (h5439 : p931 ∨ p936)
    (h5440 : p931 ∨ p937)
    (h5441 : p931 ∨ p938)
    (h5442 : p931 ∨ p939)
    (h5370 : p918 ∨ p928 ∨ (¬ p935) ∨ (¬ p936) ∨ (¬ p937) ∨ (¬ p938) ∨ (¬ p939)) : p931 ∨ p918 ∨ p928 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p931) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p928) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p935 := by
    rcases h5438 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p936 := by
    rcases h5439 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p937 := by
    rcases h5440 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p938 := by
    rcases h5441 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p939 := by
    rcases h5442 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5370 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22024 (p918 p928 p930 p931 p932 p933 p934 p935 p936 p937 p938 p939 : Prop)
    (h5345 : p918 ∨ p928 ∨ (¬ p930) ∨ (¬ p931) ∨ (¬ p932) ∨ (¬ p933) ∨ (¬ p934))
    (h5433 : p930 ∨ p935)
    (h5434 : p930 ∨ p936)
    (h5435 : p930 ∨ p937)
    (h5436 : p930 ∨ p938)
    (h5437 : p930 ∨ p939)
    (h5370 : p918 ∨ p928 ∨ (¬ p935) ∨ (¬ p936) ∨ (¬ p937) ∨ (¬ p938) ∨ (¬ p939)) : (¬ p931) ∨ (¬ p934) ∨ p928 ∨ p918 ∨ (¬ p932) ∨ (¬ p933) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p931 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p934 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p928) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p932 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p933 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p930) := by
    rcases h5345 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p935 := by
    rcases h5433 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p936 := by
    rcases h5434 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p937 := by
    rcases h5435 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p938 := by
    rcases h5436 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p939 := by
    rcases h5437 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h5370 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22025 (p918 p928 p931 p932 p933 p934 : Prop)
    (h22020 : p934 ∨ p918 ∨ p928)
    (h22021 : p933 ∨ p918 ∨ p928)
    (h22022 : p932 ∨ p918 ∨ p928)
    (h22023 : p931 ∨ p918 ∨ p928)
    (h22024 : (¬ p931) ∨ (¬ p934) ∨ p928 ∨ p918 ∨ (¬ p932) ∨ (¬ p933)) : p918 ∨ p928 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p918) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p928) := fun hu => hn (Or.inr hu)
  have u2 : p934 := by
    rcases h22020 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p933 := by
    rcases h22021 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p932 := by
    rcases h22022 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p931 := by
    rcases h22023 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22024 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22032 (p284 p287 p292 p296 p297 p298 p299 p300 : Prop)
    (h1551 : p292 ∨ p296)
    (h1552 : p292 ∨ p297)
    (h1553 : p292 ∨ p298)
    (h1554 : p292 ∨ p299)
    (h1555 : p292 ∨ p300)
    (h1487 : p284 ∨ p287 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300)) : p292 ∨ p284 ∨ p287 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p292) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p284) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p287) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p296 := by
    rcases h1551 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p297 := by
    rcases h1552 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p298 := by
    rcases h1553 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p299 := by
    rcases h1554 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p300 := by
    rcases h1555 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1487 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22033 (p284 p287 p291 p296 p297 p298 p299 p300 : Prop)
    (h1546 : p291 ∨ p296)
    (h1547 : p291 ∨ p297)
    (h1548 : p291 ∨ p298)
    (h1549 : p291 ∨ p299)
    (h1550 : p291 ∨ p300)
    (h1487 : p284 ∨ p287 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300)) : p291 ∨ p284 ∨ p287 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p291) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p284) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p287) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p296 := by
    rcases h1546 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p297 := by
    rcases h1547 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p298 := by
    rcases h1548 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p299 := by
    rcases h1549 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p300 := by
    rcases h1550 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1487 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22034 (p284 p287 p295 p296 p297 p298 p299 p300 : Prop)
    (h1566 : p295 ∨ p296)
    (h1567 : p295 ∨ p297)
    (h1568 : p295 ∨ p298)
    (h1569 : p295 ∨ p299)
    (h1570 : p295 ∨ p300)
    (h1487 : p284 ∨ p287 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300)) : p295 ∨ p284 ∨ p287 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p295) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p284) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p287) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p296 := by
    rcases h1566 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p297 := by
    rcases h1567 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p298 := by
    rcases h1568 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p299 := by
    rcases h1569 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p300 := by
    rcases h1570 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1487 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22035 (p284 p287 p294 p296 p297 p298 p299 p300 : Prop)
    (h1561 : p294 ∨ p296)
    (h1562 : p294 ∨ p297)
    (h1563 : p294 ∨ p298)
    (h1564 : p294 ∨ p299)
    (h1565 : p294 ∨ p300)
    (h1487 : p284 ∨ p287 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300)) : p294 ∨ p284 ∨ p287 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p294) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p284) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p287) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p296 := by
    rcases h1561 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p297 := by
    rcases h1562 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p298 := by
    rcases h1563 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p299 := by
    rcases h1564 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p300 := by
    rcases h1565 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1487 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22036 (p284 p287 p291 p292 p293 p294 p295 p296 p297 p298 p299 p300 : Prop)
    (h1462 : p284 ∨ p287 ∨ (¬ p291) ∨ (¬ p292) ∨ (¬ p293) ∨ (¬ p294) ∨ (¬ p295))
    (h1556 : p293 ∨ p296)
    (h1557 : p293 ∨ p297)
    (h1558 : p293 ∨ p298)
    (h1559 : p293 ∨ p299)
    (h1560 : p293 ∨ p300)
    (h1487 : p284 ∨ p287 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300)) : (¬ p294) ∨ p284 ∨ p287 ∨ (¬ p292) ∨ (¬ p291) ∨ (¬ p295) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p294 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p284) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p287) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p292 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p291 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p295 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p293) := by
    rcases h1462 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u3)
    · exact q4
    · exact False.elim (q5 u0)
    · exact False.elim (q6 u5)
  have u7 : p296 := by
    rcases h1556 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p297 := by
    rcases h1557 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p298 := by
    rcases h1558 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p299 := by
    rcases h1559 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p300 := by
    rcases h1560 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h1487 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22037 (p284 p287 p291 p292 p294 p295 : Prop)
    (h22032 : p292 ∨ p284 ∨ p287)
    (h22033 : p291 ∨ p284 ∨ p287)
    (h22034 : p295 ∨ p284 ∨ p287)
    (h22035 : p294 ∨ p284 ∨ p287)
    (h22036 : (¬ p294) ∨ p284 ∨ p287 ∨ (¬ p292) ∨ (¬ p291) ∨ (¬ p295)) : p284 ∨ p287 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p284) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p287) := fun hu => hn (Or.inr hu)
  have u2 : p292 := by
    rcases h22032 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p291 := by
    rcases h22033 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p295 := by
    rcases h22034 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p294 := by
    rcases h22035 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22036 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step22038 (p69 p86 p185 p419 p435 p860 p861 p928 p1187 p1325 p1333 p1335 p1346 p1489 p1508 : Prop)
    (h17164 : (¬ p69) ∨ (¬ p419) ∨ (¬ p1187) ∨ (¬ p1325))
    (h21904 : p1335 ∨ p1325)
    (h21656 : p1325 ∨ p1333)
    (h18722 : (¬ p69) ∨ (¬ p86) ∨ (¬ p435) ∨ (¬ p1187) ∨ (¬ p1335) ∨ (¬ p1346) ∨ (¬ p1508))
    (h18727 : (¬ p69) ∨ (¬ p185) ∨ (¬ p419) ∨ (¬ p860) ∨ (¬ p928) ∨ (¬ p1187) ∨ (¬ p1346))
    (h21548 : p1508 ∨ p1489)
    (h21340 : p860 ∨ p861)
    (h10842 : (¬ p861) ∨ (¬ p1333) ∨ (¬ p1489)) : (¬ p1346) ∨ (¬ p928) ∨ (¬ p435) ∨ (¬ p419) ∨ (¬ p185) ∨ (¬ p86) ∨ (¬ p1187) ∨ (¬ p69) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p1325) := by
    rcases h17164 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u7)
    · exact False.elim (q1 u3)
    · exact False.elim (q2 u6)
    · exact q3
  have u9 : p1335 := by
    rcases h21904 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u10 : p1333 := by
    rcases h21656 with q0 | q1
    · exact False.elim (u8 q0)
    · exact q1
  have u11 : (¬ p1508) := by
    rcases h18722 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u7)
    · exact False.elim (q1 u5)
    · exact False.elim (q2 u2)
    · exact False.elim (q3 u6)
    · exact False.elim (q4 u9)
    · exact False.elim (q5 u0)
    · exact q6
  have u12 : (¬ p860) := by
    rcases h18727 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u7)
    · exact False.elim (q1 u4)
    · exact False.elim (q2 u3)
    · exact q3
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u6)
    · exact False.elim (q6 u0)
  have u13 : p1489 := by
    rcases h21548 with q0 | q1
    · exact False.elim (u11 q0)
    · exact q1
  have u14 : p861 := by
    rcases h21340 with q0 | q1
    · exact False.elim (u12 q0)
    · exact q1
  rcases h10842 with q0 | q1 | q2
  · exact False.elim (q0 u14)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u13)

theorem step22039 (p1346 p1348 p1360 p1361 p1362 p1363 p1364 p1365 : Prop)
    (h8218 : p1360 ∨ p1361)
    (h8219 : p1360 ∨ p1362)
    (h8220 : p1360 ∨ p1363)
    (h8221 : p1360 ∨ p1364)
    (h8222 : p1360 ∨ p1365)
    (h8130 : p1346 ∨ p1348 ∨ (¬ p1361) ∨ (¬ p1362) ∨ (¬ p1363) ∨ (¬ p1364) ∨ (¬ p1365)) : p1360 ∨ p1348 ∨ p1346 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1360) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1348) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1346) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1361 := by
    rcases h8218 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1362 := by
    rcases h8219 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1363 := by
    rcases h8220 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1364 := by
    rcases h8221 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1365 := by
    rcases h8222 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8130 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22040 (p1346 p1348 p1359 p1361 p1362 p1363 p1364 p1365 : Prop)
    (h8213 : p1359 ∨ p1361)
    (h8214 : p1359 ∨ p1362)
    (h8215 : p1359 ∨ p1363)
    (h8216 : p1359 ∨ p1364)
    (h8217 : p1359 ∨ p1365)
    (h8130 : p1346 ∨ p1348 ∨ (¬ p1361) ∨ (¬ p1362) ∨ (¬ p1363) ∨ (¬ p1364) ∨ (¬ p1365)) : p1359 ∨ p1348 ∨ p1346 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1359) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1348) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1346) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1361 := by
    rcases h8213 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1362 := by
    rcases h8214 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1363 := by
    rcases h8215 with q0 | q1
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
  rcases h8130 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22041 (p1346 p1348 p1358 p1361 p1362 p1363 p1364 p1365 : Prop)
    (h8208 : p1358 ∨ p1361)
    (h8209 : p1358 ∨ p1362)
    (h8210 : p1358 ∨ p1363)
    (h8211 : p1358 ∨ p1364)
    (h8212 : p1358 ∨ p1365)
    (h8130 : p1346 ∨ p1348 ∨ (¬ p1361) ∨ (¬ p1362) ∨ (¬ p1363) ∨ (¬ p1364) ∨ (¬ p1365)) : p1358 ∨ p1348 ∨ p1346 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1358) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1348) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1346) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1361 := by
    rcases h8208 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1362 := by
    rcases h8209 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1363 := by
    rcases h8210 with q0 | q1
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
  rcases h8130 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22042 (p1346 p1348 p1357 p1361 p1362 p1363 p1364 p1365 : Prop)
    (h8203 : p1357 ∨ p1361)
    (h8204 : p1357 ∨ p1362)
    (h8205 : p1357 ∨ p1363)
    (h8206 : p1357 ∨ p1364)
    (h8207 : p1357 ∨ p1365)
    (h8130 : p1346 ∨ p1348 ∨ (¬ p1361) ∨ (¬ p1362) ∨ (¬ p1363) ∨ (¬ p1364) ∨ (¬ p1365)) : p1357 ∨ p1348 ∨ p1346 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1357) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1348) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1346) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1361 := by
    rcases h8203 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1362 := by
    rcases h8204 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1363 := by
    rcases h8205 with q0 | q1
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
  rcases h8130 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22043 (p1346 p1348 p1356 p1357 p1358 p1359 p1360 p1361 p1362 p1363 p1364 p1365 : Prop)
    (h8105 : p1346 ∨ p1348 ∨ (¬ p1356) ∨ (¬ p1357) ∨ (¬ p1358) ∨ (¬ p1359) ∨ (¬ p1360))
    (h8198 : p1356 ∨ p1361)
    (h8199 : p1356 ∨ p1362)
    (h8200 : p1356 ∨ p1363)
    (h8201 : p1356 ∨ p1364)
    (h8202 : p1356 ∨ p1365)
    (h8130 : p1346 ∨ p1348 ∨ (¬ p1361) ∨ (¬ p1362) ∨ (¬ p1363) ∨ (¬ p1364) ∨ (¬ p1365)) : (¬ p1357) ∨ (¬ p1360) ∨ p1346 ∨ p1348 ∨ (¬ p1358) ∨ (¬ p1359) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1357 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1360 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1346) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1348) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1358 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1359 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1356) := by
    rcases h8105 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p1361 := by
    rcases h8198 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1362 := by
    rcases h8199 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1363 := by
    rcases h8200 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1364 := by
    rcases h8201 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1365 := by
    rcases h8202 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h8130 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22044 (p1346 p1348 p1357 p1358 p1359 p1360 : Prop)
    (h22039 : p1360 ∨ p1348 ∨ p1346)
    (h22040 : p1359 ∨ p1348 ∨ p1346)
    (h22041 : p1358 ∨ p1348 ∨ p1346)
    (h22042 : p1357 ∨ p1348 ∨ p1346)
    (h22043 : (¬ p1357) ∨ (¬ p1360) ∨ p1346 ∨ p1348 ∨ (¬ p1358) ∨ (¬ p1359)) : p1348 ∨ p1346 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1348) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1346) := fun hu => hn (Or.inr hu)
  have u2 : p1360 := by
    rcases h22039 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1359 := by
    rcases h22040 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1358 := by
    rcases h22041 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1357 := by
    rcases h22042 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22043 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22045 (p1346 p1347 p1356 p1361 p1362 p1363 p1364 p1365 : Prop)
    (h8198 : p1356 ∨ p1361)
    (h8199 : p1356 ∨ p1362)
    (h8200 : p1356 ∨ p1363)
    (h8201 : p1356 ∨ p1364)
    (h8202 : p1356 ∨ p1365)
    (h8125 : p1346 ∨ p1347 ∨ (¬ p1361) ∨ (¬ p1362) ∨ (¬ p1363) ∨ (¬ p1364) ∨ (¬ p1365)) : p1356 ∨ p1347 ∨ p1346 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1356) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1347) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1346) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1361 := by
    rcases h8198 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1362 := by
    rcases h8199 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1363 := by
    rcases h8200 with q0 | q1
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
  rcases h8125 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22046 (p1346 p1347 p1360 p1361 p1362 p1363 p1364 p1365 : Prop)
    (h8218 : p1360 ∨ p1361)
    (h8219 : p1360 ∨ p1362)
    (h8220 : p1360 ∨ p1363)
    (h8221 : p1360 ∨ p1364)
    (h8222 : p1360 ∨ p1365)
    (h8125 : p1346 ∨ p1347 ∨ (¬ p1361) ∨ (¬ p1362) ∨ (¬ p1363) ∨ (¬ p1364) ∨ (¬ p1365)) : p1360 ∨ p1347 ∨ p1346 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1360) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1347) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1346) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1361 := by
    rcases h8218 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1362 := by
    rcases h8219 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1363 := by
    rcases h8220 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1364 := by
    rcases h8221 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1365 := by
    rcases h8222 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8125 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22047 (p1346 p1347 p1359 p1361 p1362 p1363 p1364 p1365 : Prop)
    (h8213 : p1359 ∨ p1361)
    (h8214 : p1359 ∨ p1362)
    (h8215 : p1359 ∨ p1363)
    (h8216 : p1359 ∨ p1364)
    (h8217 : p1359 ∨ p1365)
    (h8125 : p1346 ∨ p1347 ∨ (¬ p1361) ∨ (¬ p1362) ∨ (¬ p1363) ∨ (¬ p1364) ∨ (¬ p1365)) : p1359 ∨ p1347 ∨ p1346 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1359) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1347) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1346) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1361 := by
    rcases h8213 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1362 := by
    rcases h8214 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1363 := by
    rcases h8215 with q0 | q1
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
  rcases h8125 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22048 (p1346 p1347 p1358 p1361 p1362 p1363 p1364 p1365 : Prop)
    (h8208 : p1358 ∨ p1361)
    (h8209 : p1358 ∨ p1362)
    (h8210 : p1358 ∨ p1363)
    (h8211 : p1358 ∨ p1364)
    (h8212 : p1358 ∨ p1365)
    (h8125 : p1346 ∨ p1347 ∨ (¬ p1361) ∨ (¬ p1362) ∨ (¬ p1363) ∨ (¬ p1364) ∨ (¬ p1365)) : p1358 ∨ p1347 ∨ p1346 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1358) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1347) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1346) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1361 := by
    rcases h8208 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1362 := by
    rcases h8209 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1363 := by
    rcases h8210 with q0 | q1
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
  rcases h8125 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22049 (p1346 p1347 p1356 p1357 p1358 p1359 p1360 p1361 p1362 p1363 p1364 p1365 : Prop)
    (h8100 : p1346 ∨ p1347 ∨ (¬ p1356) ∨ (¬ p1357) ∨ (¬ p1358) ∨ (¬ p1359) ∨ (¬ p1360))
    (h8203 : p1357 ∨ p1361)
    (h8204 : p1357 ∨ p1362)
    (h8205 : p1357 ∨ p1363)
    (h8206 : p1357 ∨ p1364)
    (h8207 : p1357 ∨ p1365)
    (h8125 : p1346 ∨ p1347 ∨ (¬ p1361) ∨ (¬ p1362) ∨ (¬ p1363) ∨ (¬ p1364) ∨ (¬ p1365)) : (¬ p1358) ∨ (¬ p1356) ∨ p1346 ∨ p1347 ∨ (¬ p1359) ∨ (¬ p1360) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1358 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1356 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1346) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1347) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1359 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1360 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1357) := by
    rcases h8100 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u1)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u5)
  have u7 : p1361 := by
    rcases h8203 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1362 := by
    rcases h8204 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1363 := by
    rcases h8205 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1364 := by
    rcases h8206 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1365 := by
    rcases h8207 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h8125 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22050 (p1346 p1347 p1356 p1358 p1359 p1360 : Prop)
    (h22045 : p1356 ∨ p1347 ∨ p1346)
    (h22046 : p1360 ∨ p1347 ∨ p1346)
    (h22047 : p1359 ∨ p1347 ∨ p1346)
    (h22048 : p1358 ∨ p1347 ∨ p1346)
    (h22049 : (¬ p1358) ∨ (¬ p1356) ∨ p1346 ∨ p1347 ∨ (¬ p1359) ∨ (¬ p1360)) : p1347 ∨ p1346 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1347) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1346) := fun hu => hn (Or.inr hu)
  have u2 : p1356 := by
    rcases h22045 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1360 := by
    rcases h22046 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1359 := by
    rcases h22047 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1358 := by
    rcases h22048 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22049 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22051 (p1250 p1251 p1263 p1264 p1265 p1266 p1267 p1268 : Prop)
    (h7577 : p1263 ∨ p1264)
    (h7578 : p1263 ∨ p1265)
    (h7579 : p1263 ∨ p1266)
    (h7580 : p1263 ∨ p1267)
    (h7581 : p1263 ∨ p1268)
    (h7498 : p1250 ∨ p1251 ∨ (¬ p1264) ∨ (¬ p1265) ∨ (¬ p1266) ∨ (¬ p1267) ∨ (¬ p1268)) : p1263 ∨ p1251 ∨ p1250 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1263) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1251) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1250) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1264 := by
    rcases h7577 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1265 := by
    rcases h7578 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1266 := by
    rcases h7579 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1267 := by
    rcases h7580 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1268 := by
    rcases h7581 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7498 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22052 (p1250 p1251 p1262 p1264 p1265 p1266 p1267 p1268 : Prop)
    (h7572 : p1262 ∨ p1264)
    (h7573 : p1262 ∨ p1265)
    (h7574 : p1262 ∨ p1266)
    (h7575 : p1262 ∨ p1267)
    (h7576 : p1262 ∨ p1268)
    (h7498 : p1250 ∨ p1251 ∨ (¬ p1264) ∨ (¬ p1265) ∨ (¬ p1266) ∨ (¬ p1267) ∨ (¬ p1268)) : p1262 ∨ p1251 ∨ p1250 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1262) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1251) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1250) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1264 := by
    rcases h7572 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1265 := by
    rcases h7573 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1266 := by
    rcases h7574 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1267 := by
    rcases h7575 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1268 := by
    rcases h7576 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7498 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22053 (p1250 p1251 p1261 p1264 p1265 p1266 p1267 p1268 : Prop)
    (h7567 : p1261 ∨ p1264)
    (h7568 : p1261 ∨ p1265)
    (h7569 : p1261 ∨ p1266)
    (h7570 : p1261 ∨ p1267)
    (h7571 : p1261 ∨ p1268)
    (h7498 : p1250 ∨ p1251 ∨ (¬ p1264) ∨ (¬ p1265) ∨ (¬ p1266) ∨ (¬ p1267) ∨ (¬ p1268)) : p1261 ∨ p1251 ∨ p1250 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1261) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1251) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1250) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1264 := by
    rcases h7567 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1265 := by
    rcases h7568 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1266 := by
    rcases h7569 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1267 := by
    rcases h7570 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1268 := by
    rcases h7571 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7498 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22054 (p1250 p1251 p1260 p1264 p1265 p1266 p1267 p1268 : Prop)
    (h7562 : p1260 ∨ p1264)
    (h7563 : p1260 ∨ p1265)
    (h7564 : p1260 ∨ p1266)
    (h7565 : p1260 ∨ p1267)
    (h7566 : p1260 ∨ p1268)
    (h7498 : p1250 ∨ p1251 ∨ (¬ p1264) ∨ (¬ p1265) ∨ (¬ p1266) ∨ (¬ p1267) ∨ (¬ p1268)) : p1260 ∨ p1251 ∨ p1250 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1260) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1251) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1250) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1264 := by
    rcases h7562 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1265 := by
    rcases h7563 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1266 := by
    rcases h7564 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1267 := by
    rcases h7565 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1268 := by
    rcases h7566 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7498 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22055 (p1250 p1251 p1259 p1260 p1261 p1262 p1263 p1264 p1265 p1266 p1267 p1268 : Prop)
    (h7473 : p1250 ∨ p1251 ∨ (¬ p1259) ∨ (¬ p1260) ∨ (¬ p1261) ∨ (¬ p1262) ∨ (¬ p1263))
    (h7557 : p1259 ∨ p1264)
    (h7558 : p1259 ∨ p1265)
    (h7559 : p1259 ∨ p1266)
    (h7560 : p1259 ∨ p1267)
    (h7561 : p1259 ∨ p1268)
    (h7498 : p1250 ∨ p1251 ∨ (¬ p1264) ∨ (¬ p1265) ∨ (¬ p1266) ∨ (¬ p1267) ∨ (¬ p1268)) : (¬ p1260) ∨ (¬ p1263) ∨ p1250 ∨ p1251 ∨ (¬ p1261) ∨ (¬ p1262) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1260 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1263 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1250) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1251) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1259) := by
    rcases h7473 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p1264 := by
    rcases h7557 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1265 := by
    rcases h7558 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1266 := by
    rcases h7559 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1267 := by
    rcases h7560 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1268 := by
    rcases h7561 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h7498 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22056 (p1250 p1251 p1260 p1261 p1262 p1263 : Prop)
    (h22051 : p1263 ∨ p1251 ∨ p1250)
    (h22052 : p1262 ∨ p1251 ∨ p1250)
    (h22053 : p1261 ∨ p1251 ∨ p1250)
    (h22054 : p1260 ∨ p1251 ∨ p1250)
    (h22055 : (¬ p1260) ∨ (¬ p1263) ∨ p1250 ∨ p1251 ∨ (¬ p1261) ∨ (¬ p1262)) : p1251 ∨ p1250 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1251) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1250) := fun hu => hn (Or.inr hu)
  have u2 : p1263 := by
    rcases h22051 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1262 := by
    rcases h22052 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1261 := by
    rcases h22053 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1260 := by
    rcases h22054 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22055 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22057 (p187 p188 p192 p193 : Prop)
    (h13697 : p187 ∨ p192)
    (h21387 : p188 ∨ p192)
    (h13696 : (¬ p187) ∨ (¬ p188) ∨ (¬ p193)) : p192 ∨ (¬ p193) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p192) := fun hu => hn (Or.inl hu)
  have u1 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p187 := by
    rcases h13697 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u3 : p188 := by
    rcases h21387 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h13696 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)

theorem step22064 (p657 p665 p670 p675 p676 p677 p678 p679 : Prop)
    (h3859 : p670 ∨ p675)
    (h3860 : p670 ∨ p676)
    (h3861 : p670 ∨ p677)
    (h3862 : p670 ∨ p678)
    (h3863 : p670 ∨ p679)
    (h3806 : p657 ∨ p665 ∨ (¬ p675) ∨ (¬ p676) ∨ (¬ p677) ∨ (¬ p678) ∨ (¬ p679)) : p670 ∨ p665 ∨ p657 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p670) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p665) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p657) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p675 := by
    rcases h3859 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p676 := by
    rcases h3860 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p677 := by
    rcases h3861 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p678 := by
    rcases h3862 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p679 := by
    rcases h3863 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3806 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22065 (p657 p665 p674 p675 p676 p677 p678 p679 : Prop)
    (h3879 : p674 ∨ p675)
    (h3880 : p674 ∨ p676)
    (h3881 : p674 ∨ p677)
    (h3882 : p674 ∨ p678)
    (h3883 : p674 ∨ p679)
    (h3806 : p657 ∨ p665 ∨ (¬ p675) ∨ (¬ p676) ∨ (¬ p677) ∨ (¬ p678) ∨ (¬ p679)) : p674 ∨ p665 ∨ p657 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p674) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p665) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p657) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p675 := by
    rcases h3879 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p676 := by
    rcases h3880 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p677 := by
    rcases h3881 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p678 := by
    rcases h3882 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p679 := by
    rcases h3883 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3806 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22066 (p657 p665 p673 p675 p676 p677 p678 p679 : Prop)
    (h3874 : p673 ∨ p675)
    (h3875 : p673 ∨ p676)
    (h3876 : p673 ∨ p677)
    (h3877 : p673 ∨ p678)
    (h3878 : p673 ∨ p679)
    (h3806 : p657 ∨ p665 ∨ (¬ p675) ∨ (¬ p676) ∨ (¬ p677) ∨ (¬ p678) ∨ (¬ p679)) : p673 ∨ p665 ∨ p657 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p673) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p665) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p657) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p675 := by
    rcases h3874 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p676 := by
    rcases h3875 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p677 := by
    rcases h3876 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p678 := by
    rcases h3877 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p679 := by
    rcases h3878 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3806 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22067 (p657 p665 p672 p675 p676 p677 p678 p679 : Prop)
    (h3869 : p672 ∨ p675)
    (h3870 : p672 ∨ p676)
    (h3871 : p672 ∨ p677)
    (h3872 : p672 ∨ p678)
    (h3873 : p672 ∨ p679)
    (h3806 : p657 ∨ p665 ∨ (¬ p675) ∨ (¬ p676) ∨ (¬ p677) ∨ (¬ p678) ∨ (¬ p679)) : p672 ∨ p665 ∨ p657 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p672) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p665) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p657) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p675 := by
    rcases h3869 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p676 := by
    rcases h3870 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p677 := by
    rcases h3871 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p678 := by
    rcases h3872 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p679 := by
    rcases h3873 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3806 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22068 (p657 p665 p670 p671 p672 p673 p674 p675 p676 p677 p678 p679 : Prop)
    (h3781 : p657 ∨ p665 ∨ (¬ p670) ∨ (¬ p671) ∨ (¬ p672) ∨ (¬ p673) ∨ (¬ p674))
    (h3864 : p671 ∨ p675)
    (h3865 : p671 ∨ p676)
    (h3866 : p671 ∨ p677)
    (h3867 : p671 ∨ p678)
    (h3868 : p671 ∨ p679)
    (h3806 : p657 ∨ p665 ∨ (¬ p675) ∨ (¬ p676) ∨ (¬ p677) ∨ (¬ p678) ∨ (¬ p679)) : (¬ p672) ∨ p665 ∨ p657 ∨ (¬ p674) ∨ (¬ p673) ∨ (¬ p670) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p672 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p665) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p657) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p674 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p673 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p670 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p671) := by
    rcases h3781 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u5)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u3)
  have u7 : p675 := by
    rcases h3864 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p676 := by
    rcases h3865 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p677 := by
    rcases h3866 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p678 := by
    rcases h3867 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p679 := by
    rcases h3868 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h3806 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22069 (p657 p665 p670 p672 p673 p674 : Prop)
    (h22064 : p670 ∨ p665 ∨ p657)
    (h22065 : p674 ∨ p665 ∨ p657)
    (h22066 : p673 ∨ p665 ∨ p657)
    (h22067 : p672 ∨ p665 ∨ p657)
    (h22068 : (¬ p672) ∨ p665 ∨ p657 ∨ (¬ p674) ∨ (¬ p673) ∨ (¬ p670)) : p665 ∨ p657 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p665) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p657) := fun hu => hn (Or.inr hu)
  have u2 : p670 := by
    rcases h22064 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p674 := by
    rcases h22065 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p673 := by
    rcases h22066 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p672 := by
    rcases h22067 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22068 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u2)

theorem step22071 (p193 p1035 p1226 p1250 p1251 p1346 p1347 p1349 p1489 p1508 : Prop)
    (h22050 : p1347 ∨ p1346)
    (h21177 : p1349 ∨ p1346)
    (h18714 : (¬ p193) ∨ (¬ p1035) ∨ (¬ p1349) ∨ (¬ p1489))
    (h13825 : (¬ p193) ∨ (¬ p1250) ∨ p1346)
    (h21548 : p1508 ∨ p1489)
    (h22056 : p1251 ∨ p1250)
    (h18384 : (¬ p193) ∨ (¬ p1226) ∨ (¬ p1251) ∨ (¬ p1347) ∨ (¬ p1508)) : (¬ p193) ∨ (¬ p1226) ∨ p1346 ∨ (¬ p1035) := by
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
  have u2 : (¬ p1346) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1347 := by
    rcases h22050 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p1349 := by
    rcases h21177 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : (¬ p1489) := by
    rcases h18714 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u0)
    · exact False.elim (q1 u3)
    · exact False.elim (q2 u5)
    · exact q3
  have u7 : (¬ p1250) := by
    rcases h13825 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (u2 q2)
  have u8 : p1508 := by
    rcases h21548 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1251 := by
    rcases h22056 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h18384 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u8)

theorem step22075 (p136 p140 p148 p149 p150 p151 p152 p153 : Prop)
    (h776 : p148 ∨ p149)
    (h777 : p148 ∨ p150)
    (h778 : p148 ∨ p151)
    (h779 : p148 ∨ p152)
    (h780 : p148 ∨ p153)
    (h681 : p136 ∨ p140 ∨ (¬ p149) ∨ (¬ p150) ∨ (¬ p151) ∨ (¬ p152) ∨ (¬ p153)) : p148 ∨ p136 ∨ p140 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p148) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p136) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p140) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h681 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22076 (p136 p140 p144 p149 p150 p151 p152 p153 : Prop)
    (h756 : p144 ∨ p149)
    (h757 : p144 ∨ p150)
    (h758 : p144 ∨ p151)
    (h759 : p144 ∨ p152)
    (h760 : p144 ∨ p153)
    (h681 : p136 ∨ p140 ∨ (¬ p149) ∨ (¬ p150) ∨ (¬ p151) ∨ (¬ p152) ∨ (¬ p153)) : p144 ∨ p136 ∨ p140 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p144) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p136) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p140) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p149 := by
    rcases h756 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p150 := by
    rcases h757 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p151 := by
    rcases h758 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p152 := by
    rcases h759 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p153 := by
    rcases h760 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h681 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22077 (p136 p140 p147 p149 p150 p151 p152 p153 : Prop)
    (h771 : p147 ∨ p149)
    (h772 : p147 ∨ p150)
    (h773 : p147 ∨ p151)
    (h774 : p147 ∨ p152)
    (h775 : p147 ∨ p153)
    (h681 : p136 ∨ p140 ∨ (¬ p149) ∨ (¬ p150) ∨ (¬ p151) ∨ (¬ p152) ∨ (¬ p153)) : p147 ∨ p136 ∨ p140 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p147) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p136) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p140) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h681 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22078 (p136 p140 p146 p149 p150 p151 p152 p153 : Prop)
    (h766 : p146 ∨ p149)
    (h767 : p146 ∨ p150)
    (h768 : p146 ∨ p151)
    (h769 : p146 ∨ p152)
    (h770 : p146 ∨ p153)
    (h681 : p136 ∨ p140 ∨ (¬ p149) ∨ (¬ p150) ∨ (¬ p151) ∨ (¬ p152) ∨ (¬ p153)) : p146 ∨ p136 ∨ p140 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p146) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p136) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p140) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h681 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22079 (p136 p140 p144 p145 p146 p147 p148 p149 p150 p151 p152 p153 : Prop)
    (h656 : p136 ∨ p140 ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p147) ∨ (¬ p148))
    (h761 : p145 ∨ p149)
    (h762 : p145 ∨ p150)
    (h763 : p145 ∨ p151)
    (h764 : p145 ∨ p152)
    (h765 : p145 ∨ p153)
    (h681 : p136 ∨ p140 ∨ (¬ p149) ∨ (¬ p150) ∨ (¬ p151) ∨ (¬ p152) ∨ (¬ p153)) : (¬ p146) ∨ p136 ∨ p140 ∨ (¬ p147) ∨ (¬ p144) ∨ (¬ p148) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p146 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p136) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p140) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p147 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p144 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p148 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p145) := by
    rcases h656 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u3)
    · exact False.elim (q6 u5)
  have u7 : p149 := by
    rcases h761 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p150 := by
    rcases h762 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p151 := by
    rcases h763 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p152 := by
    rcases h764 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p153 := by
    rcases h765 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h681 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22080 (p136 p140 p144 p146 p147 p148 : Prop)
    (h22075 : p148 ∨ p136 ∨ p140)
    (h22076 : p144 ∨ p136 ∨ p140)
    (h22077 : p147 ∨ p136 ∨ p140)
    (h22078 : p146 ∨ p136 ∨ p140)
    (h22079 : (¬ p146) ∨ p136 ∨ p140 ∨ (¬ p147) ∨ (¬ p144) ∨ (¬ p148)) : p136 ∨ p140 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p136) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p140) := fun hu => hn (Or.inr hu)
  have u2 : p148 := by
    rcases h22075 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p144 := by
    rcases h22076 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p147 := by
    rcases h22077 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p146 := by
    rcases h22078 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22079 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u2)

theorem step22082 (p304 p350 p364 p368 p438 p687 : Prop)
    (h16999 : (¬ p304) ∨ (¬ p350) ∨ (¬ p368) ∨ (¬ p438) ∨ (¬ p687))
    (h12391 : (¬ p364) ∨ (¬ p438) ∨ (¬ p687))
    (h21352 : p368 ∨ p364) : (¬ p687) ∨ (¬ p438) ∨ (¬ p304) ∨ (¬ p350) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p368) := by
    rcases h16999 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u2)
    · exact False.elim (q1 u3)
    · exact q2
    · exact False.elim (q3 u1)
    · exact False.elim (q4 u0)
  have u5 : (¬ p364) := by
    rcases h12391 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u1)
    · exact False.elim (q2 u0)
  rcases h21352 with q0 | q1
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)

theorem step22083 (p789 p860 p869 p870 p871 p872 p873 p874 : Prop)
    (h5047 : p869 ∨ p870)
    (h5048 : p869 ∨ p871)
    (h5049 : p869 ∨ p872)
    (h5050 : p869 ∨ p873)
    (h5051 : p869 ∨ p874)
    (h4974 : p789 ∨ p860 ∨ (¬ p870) ∨ (¬ p871) ∨ (¬ p872) ∨ (¬ p873) ∨ (¬ p874)) : p869 ∨ p789 ∨ p860 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p869) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p789) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p860) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p870 := by
    rcases h5047 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p871 := by
    rcases h5048 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p872 := by
    rcases h5049 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p873 := by
    rcases h5050 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p874 := by
    rcases h5051 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4974 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22084 (p789 p860 p868 p870 p871 p872 p873 p874 : Prop)
    (h5042 : p868 ∨ p870)
    (h5043 : p868 ∨ p871)
    (h5044 : p868 ∨ p872)
    (h5045 : p868 ∨ p873)
    (h5046 : p868 ∨ p874)
    (h4974 : p789 ∨ p860 ∨ (¬ p870) ∨ (¬ p871) ∨ (¬ p872) ∨ (¬ p873) ∨ (¬ p874)) : p868 ∨ p789 ∨ p860 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p868) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p789) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p860) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p870 := by
    rcases h5042 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p871 := by
    rcases h5043 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p872 := by
    rcases h5044 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p873 := by
    rcases h5045 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p874 := by
    rcases h5046 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4974 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22085 (p789 p860 p867 p870 p871 p872 p873 p874 : Prop)
    (h5037 : p867 ∨ p870)
    (h5038 : p867 ∨ p871)
    (h5039 : p867 ∨ p872)
    (h5040 : p867 ∨ p873)
    (h5041 : p867 ∨ p874)
    (h4974 : p789 ∨ p860 ∨ (¬ p870) ∨ (¬ p871) ∨ (¬ p872) ∨ (¬ p873) ∨ (¬ p874)) : p867 ∨ p789 ∨ p860 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p867) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p789) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p860) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p870 := by
    rcases h5037 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p871 := by
    rcases h5038 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p872 := by
    rcases h5039 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p873 := by
    rcases h5040 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p874 := by
    rcases h5041 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4974 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22086 (p789 p860 p866 p870 p871 p872 p873 p874 : Prop)
    (h5032 : p866 ∨ p870)
    (h5033 : p866 ∨ p871)
    (h5034 : p866 ∨ p872)
    (h5035 : p866 ∨ p873)
    (h5036 : p866 ∨ p874)
    (h4974 : p789 ∨ p860 ∨ (¬ p870) ∨ (¬ p871) ∨ (¬ p872) ∨ (¬ p873) ∨ (¬ p874)) : p866 ∨ p789 ∨ p860 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p866) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p789) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p860) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p870 := by
    rcases h5032 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p871 := by
    rcases h5033 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p872 := by
    rcases h5034 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p873 := by
    rcases h5035 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p874 := by
    rcases h5036 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4974 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22087 (p789 p860 p865 p866 p867 p868 p869 p870 p871 p872 p873 p874 : Prop)
    (h4949 : p789 ∨ p860 ∨ (¬ p865) ∨ (¬ p866) ∨ (¬ p867) ∨ (¬ p868) ∨ (¬ p869))
    (h5027 : p865 ∨ p870)
    (h5028 : p865 ∨ p871)
    (h5029 : p865 ∨ p872)
    (h5030 : p865 ∨ p873)
    (h5031 : p865 ∨ p874)
    (h4974 : p789 ∨ p860 ∨ (¬ p870) ∨ (¬ p871) ∨ (¬ p872) ∨ (¬ p873) ∨ (¬ p874)) : (¬ p866) ∨ (¬ p869) ∨ p789 ∨ p860 ∨ (¬ p867) ∨ (¬ p868) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p866 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p869 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p860) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p867 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p868 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p865) := by
    rcases h4949 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p870 := by
    rcases h5027 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p871 := by
    rcases h5028 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p872 := by
    rcases h5029 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p873 := by
    rcases h5030 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p874 := by
    rcases h5031 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h4974 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22088 (p789 p860 p866 p867 p868 p869 : Prop)
    (h22083 : p869 ∨ p789 ∨ p860)
    (h22084 : p868 ∨ p789 ∨ p860)
    (h22085 : p867 ∨ p789 ∨ p860)
    (h22086 : p866 ∨ p789 ∨ p860)
    (h22087 : (¬ p866) ∨ (¬ p869) ∨ p789 ∨ p860 ∨ (¬ p867) ∨ (¬ p868)) : p789 ∨ p860 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p789) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p860) := fun hu => hn (Or.inr hu)
  have u2 : p869 := by
    rcases h22083 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p868 := by
    rcases h22084 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p867 := by
    rcases h22085 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p866 := by
    rcases h22086 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22087 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22090 (p234 p1188 p1200 p1201 p1202 p1203 p1204 p1205 : Prop)
    (h7183 : p1200 ∨ p1201)
    (h7184 : p1200 ∨ p1202)
    (h7185 : p1200 ∨ p1203)
    (h7186 : p1200 ∨ p1204)
    (h7187 : p1200 ∨ p1205)
    (h7090 : p234 ∨ p1188 ∨ (¬ p1201) ∨ (¬ p1202) ∨ (¬ p1203) ∨ (¬ p1204) ∨ (¬ p1205)) : p1200 ∨ p1188 ∨ p234 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1200) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1188) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p234) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h7090 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22091 (p234 p1188 p1199 p1201 p1202 p1203 p1204 p1205 : Prop)
    (h7178 : p1199 ∨ p1201)
    (h7179 : p1199 ∨ p1202)
    (h7180 : p1199 ∨ p1203)
    (h7181 : p1199 ∨ p1204)
    (h7182 : p1199 ∨ p1205)
    (h7090 : p234 ∨ p1188 ∨ (¬ p1201) ∨ (¬ p1202) ∨ (¬ p1203) ∨ (¬ p1204) ∨ (¬ p1205)) : p1199 ∨ p1188 ∨ p234 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1199) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1188) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h7090 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22092 (p234 p1188 p1198 p1201 p1202 p1203 p1204 p1205 : Prop)
    (h7173 : p1198 ∨ p1201)
    (h7174 : p1198 ∨ p1202)
    (h7175 : p1198 ∨ p1203)
    (h7176 : p1198 ∨ p1204)
    (h7177 : p1198 ∨ p1205)
    (h7090 : p234 ∨ p1188 ∨ (¬ p1201) ∨ (¬ p1202) ∨ (¬ p1203) ∨ (¬ p1204) ∨ (¬ p1205)) : p1198 ∨ p1188 ∨ p234 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1198) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1188) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h7090 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22093 (p234 p1188 p1197 p1201 p1202 p1203 p1204 p1205 : Prop)
    (h7168 : p1197 ∨ p1201)
    (h7169 : p1197 ∨ p1202)
    (h7170 : p1197 ∨ p1203)
    (h7171 : p1197 ∨ p1204)
    (h7172 : p1197 ∨ p1205)
    (h7090 : p234 ∨ p1188 ∨ (¬ p1201) ∨ (¬ p1202) ∨ (¬ p1203) ∨ (¬ p1204) ∨ (¬ p1205)) : p1197 ∨ p1188 ∨ p234 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1197) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1188) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h7090 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22094 (p234 p1188 p1196 p1197 p1198 p1199 p1200 p1201 p1202 p1203 p1204 p1205 : Prop)
    (h7065 : p234 ∨ p1188 ∨ (¬ p1196) ∨ (¬ p1197) ∨ (¬ p1198) ∨ (¬ p1199) ∨ (¬ p1200))
    (h7163 : p1196 ∨ p1201)
    (h7164 : p1196 ∨ p1202)
    (h7165 : p1196 ∨ p1203)
    (h7166 : p1196 ∨ p1204)
    (h7167 : p1196 ∨ p1205)
    (h7090 : p234 ∨ p1188 ∨ (¬ p1201) ∨ (¬ p1202) ∨ (¬ p1203) ∨ (¬ p1204) ∨ (¬ p1205)) : (¬ p1197) ∨ p1188 ∨ p234 ∨ (¬ p1199) ∨ (¬ p1198) ∨ (¬ p1200) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1197 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1188) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p234) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1199 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1198 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1200 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1196) := by
    rcases h7065 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u3)
    · exact False.elim (q6 u5)
  have u7 : p1201 := by
    rcases h7163 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1202 := by
    rcases h7164 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1203 := by
    rcases h7165 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1204 := by
    rcases h7166 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1205 := by
    rcases h7167 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h7090 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22095 (p234 p1188 p1197 p1198 p1199 p1200 : Prop)
    (h22090 : p1200 ∨ p1188 ∨ p234)
    (h22091 : p1199 ∨ p1188 ∨ p234)
    (h22092 : p1198 ∨ p1188 ∨ p234)
    (h22093 : p1197 ∨ p1188 ∨ p234)
    (h22094 : (¬ p1197) ∨ p1188 ∨ p234 ∨ (¬ p1199) ∨ (¬ p1198) ∨ (¬ p1200)) : p1188 ∨ p234 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1188) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p234) := fun hu => hn (Or.inr hu)
  have u2 : p1200 := by
    rcases h22090 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1199 := by
    rcases h22091 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1198 := by
    rcases h22092 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1197 := by
    rcases h22093 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22094 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u2)

theorem step22096 (p8 p21 p69 p101 p323 p329 p350 p419 p434 p438 p600 p728 p734 p996 p1100 p1187 p1188 p1328 p1334 p1366 p1542 p1545 : Prop)
    (h21912 : p1100)
    (h5837 : (¬ p419) ∨ (¬ p996))
    (h12387 : p996 ∨ (¬ p1328) ∨ (¬ p1366))
    (h18430 : (¬ p69) ∨ (¬ p101) ∨ (¬ p329) ∨ (¬ p1188) ∨ (¬ p1366) ∨ (¬ p1545))
    (h21365 : p1334 ∨ p1328)
    (h20851 : p1542 ∨ p1545)
    (h18304 : (¬ p8) ∨ (¬ p69) ∨ (¬ p419) ∨ (¬ p728) ∨ (¬ p1100) ∨ (¬ p1187) ∨ (¬ p1334))
    (h17955 : (¬ p21) ∨ (¬ p101) ∨ (¬ p350) ∨ (¬ p438) ∨ (¬ p600) ∨ (¬ p1542))
    (h20753 : p728 ∨ p734)
    (h21060 : p438 ∨ p434)
    (h20120 : (¬ p101) ∨ (¬ p323) ∨ (¬ p434) ∨ (¬ p734)) : (¬ p1366) ∨ (¬ p419) ∨ (¬ p1188) ∨ (¬ p1187) ∨ (¬ p350) ∨ (¬ p101) ∨ (¬ p69) ∨ (¬ p600) ∨ (¬ p323) ∨ (¬ p329) ∨ (¬ p8) ∨ (¬ p21) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p600 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p329 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p21 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))
  have u12 : p1100 := by
    exact h21912
  have u13 : (¬ p996) := by
    rcases h5837 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  have u14 : (¬ p1328) := by
    rcases h12387 with q0 | q1 | q2
    · exact False.elim (u13 q0)
    · exact q1
    · exact False.elim (q2 u0)
  have u15 : (¬ p1545) := by
    rcases h18430 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u6)
    · exact False.elim (q1 u5)
    · exact False.elim (q2 u9)
    · exact False.elim (q3 u2)
    · exact False.elim (q4 u0)
    · exact q5
  have u16 : p1334 := by
    rcases h21365 with q0 | q1
    · exact q0
    · exact False.elim (u14 q1)
  have u17 : p1542 := by
    rcases h20851 with q0 | q1
    · exact q0
    · exact False.elim (u15 q1)
  have u18 : (¬ p728) := by
    rcases h18304 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u10)
    · exact False.elim (q1 u6)
    · exact False.elim (q2 u1)
    · exact q3
    · exact False.elim (q4 u12)
    · exact False.elim (q5 u3)
    · exact False.elim (q6 u16)
  have u19 : (¬ p438) := by
    rcases h17955 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u11)
    · exact False.elim (q1 u5)
    · exact False.elim (q2 u4)
    · exact q3
    · exact False.elim (q4 u7)
    · exact False.elim (q5 u17)
  have u20 : p734 := by
    rcases h20753 with q0 | q1
    · exact False.elim (u18 q0)
    · exact q1
  have u21 : p434 := by
    rcases h21060 with q0 | q1
    · exact False.elim (u19 q0)
    · exact q1
  rcases h20120 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u21)
  · exact False.elim (q3 u20)

theorem step22100 (p256 p261 p273 p274 p275 p276 p277 p278 : Prop)
    (h1433 : p273 ∨ p274)
    (h1434 : p273 ∨ p275)
    (h1435 : p273 ∨ p276)
    (h1436 : p273 ∨ p277)
    (h1437 : p273 ∨ p278)
    (h1340 : p256 ∨ p261 ∨ (¬ p274) ∨ (¬ p275) ∨ (¬ p276) ∨ (¬ p277) ∨ (¬ p278)) : p273 ∨ p261 ∨ p256 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p273) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p261) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p256) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p274 := by
    rcases h1433 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p275 := by
    rcases h1434 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p276 := by
    rcases h1435 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p277 := by
    rcases h1436 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p278 := by
    rcases h1437 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1340 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22101 (p256 p261 p272 p274 p275 p276 p277 p278 : Prop)
    (h1428 : p272 ∨ p274)
    (h1429 : p272 ∨ p275)
    (h1430 : p272 ∨ p276)
    (h1431 : p272 ∨ p277)
    (h1432 : p272 ∨ p278)
    (h1340 : p256 ∨ p261 ∨ (¬ p274) ∨ (¬ p275) ∨ (¬ p276) ∨ (¬ p277) ∨ (¬ p278)) : p272 ∨ p261 ∨ p256 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p272) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p261) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p256) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p274 := by
    rcases h1428 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p275 := by
    rcases h1429 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p276 := by
    rcases h1430 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p277 := by
    rcases h1431 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p278 := by
    rcases h1432 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1340 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22102 (p256 p261 p271 p274 p275 p276 p277 p278 : Prop)
    (h1423 : p271 ∨ p274)
    (h1424 : p271 ∨ p275)
    (h1425 : p271 ∨ p276)
    (h1426 : p271 ∨ p277)
    (h1427 : p271 ∨ p278)
    (h1340 : p256 ∨ p261 ∨ (¬ p274) ∨ (¬ p275) ∨ (¬ p276) ∨ (¬ p277) ∨ (¬ p278)) : p271 ∨ p261 ∨ p256 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p271) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p261) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p256) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p274 := by
    rcases h1423 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p275 := by
    rcases h1424 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p276 := by
    rcases h1425 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p277 := by
    rcases h1426 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p278 := by
    rcases h1427 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1340 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22103 (p256 p261 p270 p274 p275 p276 p277 p278 : Prop)
    (h1418 : p270 ∨ p274)
    (h1419 : p270 ∨ p275)
    (h1420 : p270 ∨ p276)
    (h1421 : p270 ∨ p277)
    (h1422 : p270 ∨ p278)
    (h1340 : p256 ∨ p261 ∨ (¬ p274) ∨ (¬ p275) ∨ (¬ p276) ∨ (¬ p277) ∨ (¬ p278)) : p270 ∨ p261 ∨ p256 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p270) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p261) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p256) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p274 := by
    rcases h1418 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p275 := by
    rcases h1419 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p276 := by
    rcases h1420 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p277 := by
    rcases h1421 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p278 := by
    rcases h1422 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1340 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22104 (p256 p261 p269 p274 p275 p276 p277 p278 : Prop)
    (h1413 : p269 ∨ p274)
    (h1414 : p269 ∨ p275)
    (h1415 : p269 ∨ p276)
    (h1416 : p269 ∨ p277)
    (h1417 : p269 ∨ p278)
    (h1340 : p256 ∨ p261 ∨ (¬ p274) ∨ (¬ p275) ∨ (¬ p276) ∨ (¬ p277) ∨ (¬ p278)) : p269 ∨ p261 ∨ p256 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p269) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p261) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p256) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p274 := by
    rcases h1413 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p275 := by
    rcases h1414 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p276 := by
    rcases h1415 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p277 := by
    rcases h1416 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p278 := by
    rcases h1417 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1340 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22105 (p256 p261 p269 p270 p271 p272 p273 : Prop)
    (h22100 : p273 ∨ p261 ∨ p256)
    (h22101 : p272 ∨ p261 ∨ p256)
    (h22102 : p271 ∨ p261 ∨ p256)
    (h22103 : p270 ∨ p261 ∨ p256)
    (h22104 : p269 ∨ p261 ∨ p256)
    (h1315 : p256 ∨ p261 ∨ (¬ p269) ∨ (¬ p270) ∨ (¬ p271) ∨ (¬ p272) ∨ (¬ p273)) : p261 ∨ p256 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p261) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p256) := fun hu => hn (Or.inr hu)
  have u2 : p273 := by
    rcases h22100 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p272 := by
    rcases h22101 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p271 := by
    rcases h22102 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p270 := by
    rcases h22103 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p269 := by
    rcases h22104 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h1315 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u2)

theorem step22106 (p790 p815 p827 p828 p829 p830 p831 p832 : Prop)
    (h4789 : p827 ∨ p828)
    (h4790 : p827 ∨ p829)
    (h4791 : p827 ∨ p830)
    (h4792 : p827 ∨ p831)
    (h4793 : p827 ∨ p832)
    (h4696 : p790 ∨ p815 ∨ (¬ p828) ∨ (¬ p829) ∨ (¬ p830) ∨ (¬ p831) ∨ (¬ p832)) : p827 ∨ p815 ∨ p790 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p827) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p815) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p790) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p828 := by
    rcases h4789 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p829 := by
    rcases h4790 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p830 := by
    rcases h4791 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p831 := by
    rcases h4792 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p832 := by
    rcases h4793 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4696 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22107 (p790 p815 p826 p828 p829 p830 p831 p832 : Prop)
    (h4784 : p826 ∨ p828)
    (h4785 : p826 ∨ p829)
    (h4786 : p826 ∨ p830)
    (h4787 : p826 ∨ p831)
    (h4788 : p826 ∨ p832)
    (h4696 : p790 ∨ p815 ∨ (¬ p828) ∨ (¬ p829) ∨ (¬ p830) ∨ (¬ p831) ∨ (¬ p832)) : p826 ∨ p815 ∨ p790 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p826) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p815) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p790) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h4696 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22108 (p790 p815 p825 p828 p829 p830 p831 p832 : Prop)
    (h4779 : p825 ∨ p828)
    (h4780 : p825 ∨ p829)
    (h4781 : p825 ∨ p830)
    (h4782 : p825 ∨ p831)
    (h4783 : p825 ∨ p832)
    (h4696 : p790 ∨ p815 ∨ (¬ p828) ∨ (¬ p829) ∨ (¬ p830) ∨ (¬ p831) ∨ (¬ p832)) : p825 ∨ p815 ∨ p790 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p825) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p815) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p790) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h4696 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22109 (p790 p815 p824 p828 p829 p830 p831 p832 : Prop)
    (h4774 : p824 ∨ p828)
    (h4775 : p824 ∨ p829)
    (h4776 : p824 ∨ p830)
    (h4777 : p824 ∨ p831)
    (h4778 : p824 ∨ p832)
    (h4696 : p790 ∨ p815 ∨ (¬ p828) ∨ (¬ p829) ∨ (¬ p830) ∨ (¬ p831) ∨ (¬ p832)) : p824 ∨ p815 ∨ p790 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p824) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p815) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p790) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h4696 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22110 (p790 p815 p823 p824 p825 p826 p827 p828 p829 p830 p831 p832 : Prop)
    (h4671 : p790 ∨ p815 ∨ (¬ p823) ∨ (¬ p824) ∨ (¬ p825) ∨ (¬ p826) ∨ (¬ p827))
    (h4769 : p823 ∨ p828)
    (h4770 : p823 ∨ p829)
    (h4771 : p823 ∨ p830)
    (h4772 : p823 ∨ p831)
    (h4773 : p823 ∨ p832)
    (h4696 : p790 ∨ p815 ∨ (¬ p828) ∨ (¬ p829) ∨ (¬ p830) ∨ (¬ p831) ∨ (¬ p832)) : (¬ p824) ∨ (¬ p827) ∨ p790 ∨ p815 ∨ (¬ p825) ∨ (¬ p826) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p824 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p827 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p815) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p825 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p826 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p823) := by
    rcases h4671 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p828 := by
    rcases h4769 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p829 := by
    rcases h4770 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p830 := by
    rcases h4771 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p831 := by
    rcases h4772 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p832 := by
    rcases h4773 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h4696 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22111 (p790 p815 p824 p825 p826 p827 : Prop)
    (h22106 : p827 ∨ p815 ∨ p790)
    (h22107 : p826 ∨ p815 ∨ p790)
    (h22108 : p825 ∨ p815 ∨ p790)
    (h22109 : p824 ∨ p815 ∨ p790)
    (h22110 : (¬ p824) ∨ (¬ p827) ∨ p790 ∨ p815 ∨ (¬ p825) ∨ (¬ p826)) : p815 ∨ p790 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p815) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p790) := fun hu => hn (Or.inr hu)
  have u2 : p827 := by
    rcases h22106 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p826 := by
    rcases h22107 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p825 := by
    rcases h22108 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p824 := by
    rcases h22109 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22110 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22112 (p159 p1273 p1280 p1281 p1282 p1283 p1284 p1285 : Prop)
    (h7702 : p1280 ∨ p1281)
    (h7703 : p1280 ∨ p1282)
    (h7704 : p1280 ∨ p1283)
    (h7705 : p1280 ∨ p1284)
    (h7706 : p1280 ∨ p1285)
    (h7609 : p159 ∨ p1273 ∨ (¬ p1281) ∨ (¬ p1282) ∨ (¬ p1283) ∨ (¬ p1284) ∨ (¬ p1285)) : p1280 ∨ p159 ∨ p1273 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1280) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p159) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1273) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1281 := by
    rcases h7702 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1282 := by
    rcases h7703 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1283 := by
    rcases h7704 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1284 := by
    rcases h7705 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1285 := by
    rcases h7706 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7609 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22113 (p159 p1273 p1279 p1281 p1282 p1283 p1284 p1285 : Prop)
    (h7697 : p1279 ∨ p1281)
    (h7698 : p1279 ∨ p1282)
    (h7699 : p1279 ∨ p1283)
    (h7700 : p1279 ∨ p1284)
    (h7701 : p1279 ∨ p1285)
    (h7609 : p159 ∨ p1273 ∨ (¬ p1281) ∨ (¬ p1282) ∨ (¬ p1283) ∨ (¬ p1284) ∨ (¬ p1285)) : p1279 ∨ p159 ∨ p1273 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1279) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p159) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1273) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1281 := by
    rcases h7697 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1282 := by
    rcases h7698 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1283 := by
    rcases h7699 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1284 := by
    rcases h7700 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1285 := by
    rcases h7701 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7609 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22114 (p159 p1273 p1278 p1281 p1282 p1283 p1284 p1285 : Prop)
    (h7692 : p1278 ∨ p1281)
    (h7693 : p1278 ∨ p1282)
    (h7694 : p1278 ∨ p1283)
    (h7695 : p1278 ∨ p1284)
    (h7696 : p1278 ∨ p1285)
    (h7609 : p159 ∨ p1273 ∨ (¬ p1281) ∨ (¬ p1282) ∨ (¬ p1283) ∨ (¬ p1284) ∨ (¬ p1285)) : p1278 ∨ p159 ∨ p1273 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1278) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p159) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1273) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1281 := by
    rcases h7692 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1282 := by
    rcases h7693 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1283 := by
    rcases h7694 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1284 := by
    rcases h7695 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1285 := by
    rcases h7696 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7609 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22115 (p159 p1273 p1277 p1281 p1282 p1283 p1284 p1285 : Prop)
    (h7687 : p1277 ∨ p1281)
    (h7688 : p1277 ∨ p1282)
    (h7689 : p1277 ∨ p1283)
    (h7690 : p1277 ∨ p1284)
    (h7691 : p1277 ∨ p1285)
    (h7609 : p159 ∨ p1273 ∨ (¬ p1281) ∨ (¬ p1282) ∨ (¬ p1283) ∨ (¬ p1284) ∨ (¬ p1285)) : p1277 ∨ p159 ∨ p1273 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1277) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p159) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1273) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1281 := by
    rcases h7687 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1282 := by
    rcases h7688 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1283 := by
    rcases h7689 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1284 := by
    rcases h7690 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1285 := by
    rcases h7691 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7609 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22116 (p159 p1273 p1276 p1277 p1278 p1279 p1280 p1281 p1282 p1283 p1284 p1285 : Prop)
    (h7584 : p159 ∨ p1273 ∨ (¬ p1276) ∨ (¬ p1277) ∨ (¬ p1278) ∨ (¬ p1279) ∨ (¬ p1280))
    (h7682 : p1276 ∨ p1281)
    (h7683 : p1276 ∨ p1282)
    (h7684 : p1276 ∨ p1283)
    (h7685 : p1276 ∨ p1284)
    (h7686 : p1276 ∨ p1285)
    (h7609 : p159 ∨ p1273 ∨ (¬ p1281) ∨ (¬ p1282) ∨ (¬ p1283) ∨ (¬ p1284) ∨ (¬ p1285)) : (¬ p1277) ∨ (¬ p1280) ∨ p1273 ∨ p159 ∨ (¬ p1278) ∨ (¬ p1279) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1277 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1280 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1273) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p159) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1278 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1279 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1276) := by
    rcases h7584 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p1281 := by
    rcases h7682 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1282 := by
    rcases h7683 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1283 := by
    rcases h7684 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1284 := by
    rcases h7685 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1285 := by
    rcases h7686 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h7609 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22117 (p159 p1273 p1277 p1278 p1279 p1280 : Prop)
    (h22112 : p1280 ∨ p159 ∨ p1273)
    (h22113 : p1279 ∨ p159 ∨ p1273)
    (h22114 : p1278 ∨ p159 ∨ p1273)
    (h22115 : p1277 ∨ p159 ∨ p1273)
    (h22116 : (¬ p1277) ∨ (¬ p1280) ∨ p1273 ∨ p159 ∨ (¬ p1278) ∨ (¬ p1279)) : p159 ∨ p1273 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p159) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1273) := fun hu => hn (Or.inr hu)
  have u2 : p1280 := by
    rcases h22112 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1279 := by
    rcases h22113 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1278 := by
    rcases h22114 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1277 := by
    rcases h22115 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22116 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22118 (p1118 p1122 p1125 p1126 p1127 p1128 p1129 p1134 : Prop)
    (h6712 : p1125 ∨ p1134)
    (h6717 : p1126 ∨ p1134)
    (h6722 : p1127 ∨ p1134)
    (h6727 : p1128 ∨ p1134)
    (h6732 : p1129 ∨ p1134)
    (h6614 : p1118 ∨ p1122 ∨ (¬ p1125) ∨ (¬ p1126) ∨ (¬ p1127) ∨ (¬ p1128) ∨ (¬ p1129)) : p1134 ∨ p1122 ∨ p1118 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1134) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1122) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1118) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1125 := by
    rcases h6712 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1126 := by
    rcases h6717 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1127 := by
    rcases h6722 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1128 := by
    rcases h6727 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1129 := by
    rcases h6732 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6614 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22119 (p1118 p1122 p1125 p1126 p1127 p1128 p1129 p1133 : Prop)
    (h6711 : p1125 ∨ p1133)
    (h6716 : p1126 ∨ p1133)
    (h6721 : p1127 ∨ p1133)
    (h6726 : p1128 ∨ p1133)
    (h6731 : p1129 ∨ p1133)
    (h6614 : p1118 ∨ p1122 ∨ (¬ p1125) ∨ (¬ p1126) ∨ (¬ p1127) ∨ (¬ p1128) ∨ (¬ p1129)) : p1133 ∨ p1122 ∨ p1118 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1133) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1122) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1118) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1125 := by
    rcases h6711 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1126 := by
    rcases h6716 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1127 := by
    rcases h6721 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1128 := by
    rcases h6726 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1129 := by
    rcases h6731 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6614 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22120 (p1118 p1122 p1125 p1126 p1127 p1128 p1129 p1132 : Prop)
    (h6710 : p1125 ∨ p1132)
    (h6715 : p1126 ∨ p1132)
    (h6720 : p1127 ∨ p1132)
    (h6725 : p1128 ∨ p1132)
    (h6730 : p1129 ∨ p1132)
    (h6614 : p1118 ∨ p1122 ∨ (¬ p1125) ∨ (¬ p1126) ∨ (¬ p1127) ∨ (¬ p1128) ∨ (¬ p1129)) : p1132 ∨ p1122 ∨ p1118 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1132) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1122) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1118) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1125 := by
    rcases h6710 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1126 := by
    rcases h6715 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1127 := by
    rcases h6720 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1128 := by
    rcases h6725 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1129 := by
    rcases h6730 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6614 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22121 (p1118 p1122 p1125 p1126 p1127 p1128 p1129 p1131 : Prop)
    (h6709 : p1125 ∨ p1131)
    (h6714 : p1126 ∨ p1131)
    (h6719 : p1127 ∨ p1131)
    (h6724 : p1128 ∨ p1131)
    (h6729 : p1129 ∨ p1131)
    (h6614 : p1118 ∨ p1122 ∨ (¬ p1125) ∨ (¬ p1126) ∨ (¬ p1127) ∨ (¬ p1128) ∨ (¬ p1129)) : p1131 ∨ p1122 ∨ p1118 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1131) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1122) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1118) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1125 := by
    rcases h6709 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1126 := by
    rcases h6714 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1127 := by
    rcases h6719 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1128 := by
    rcases h6724 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1129 := by
    rcases h6729 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6614 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22123 (p63 p87 p88 p91 p92 p93 p94 p95 : Prop)
    (h21841 : p95 ∨ p87 ∨ p63)
    (h21842 : p94 ∨ p87 ∨ p63)
    (h21843 : p93 ∨ p87 ∨ p63)
    (h21844 : p92 ∨ p87 ∨ p63)
    (h21928 : p91 ∨ p87 ∨ p63)
    (h414 : p87 ∨ p88 ∨ (¬ p91) ∨ (¬ p92) ∨ (¬ p93) ∨ (¬ p94) ∨ (¬ p95)) : p87 ∨ p88 ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p87) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p88) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p95 := by
    rcases h21841 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u4 : p94 := by
    rcases h21842 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u5 : p93 := by
    rcases h21843 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u6 : p92 := by
    rcases h21844 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u7 : p91 := by
    rcases h21928 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  rcases h414 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u3)

theorem step22124 (p45 p47 p55 p56 p57 p58 p59 p60 : Prop)
    (h253 : p55 ∨ p56)
    (h254 : p55 ∨ p57)
    (h255 : p55 ∨ p58)
    (h256 : p55 ∨ p59)
    (h257 : p55 ∨ p60)
    (h168 : p45 ∨ p47 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60)) : p55 ∨ p45 ∨ p47 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p55) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p45) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p47) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p56 := by
    rcases h253 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p57 := by
    rcases h254 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p58 := by
    rcases h255 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p59 := by
    rcases h256 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p60 := by
    rcases h257 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h168 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22125 (p45 p47 p54 p56 p57 p58 p59 p60 : Prop)
    (h248 : p54 ∨ p56)
    (h249 : p54 ∨ p57)
    (h250 : p54 ∨ p58)
    (h251 : p54 ∨ p59)
    (h252 : p54 ∨ p60)
    (h168 : p45 ∨ p47 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60)) : p54 ∨ p45 ∨ p47 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p54) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p45) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p47) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p56 := by
    rcases h248 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p57 := by
    rcases h249 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p58 := by
    rcases h250 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p59 := by
    rcases h251 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p60 := by
    rcases h252 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h168 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22126 (p45 p47 p53 p56 p57 p58 p59 p60 : Prop)
    (h243 : p53 ∨ p56)
    (h244 : p53 ∨ p57)
    (h245 : p53 ∨ p58)
    (h246 : p53 ∨ p59)
    (h247 : p53 ∨ p60)
    (h168 : p45 ∨ p47 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60)) : p53 ∨ p45 ∨ p47 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p53) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p45) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p47) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p56 := by
    rcases h243 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p57 := by
    rcases h244 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p58 := by
    rcases h245 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p59 := by
    rcases h246 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p60 := by
    rcases h247 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h168 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22127 (p45 p47 p52 p56 p57 p58 p59 p60 : Prop)
    (h238 : p52 ∨ p56)
    (h239 : p52 ∨ p57)
    (h240 : p52 ∨ p58)
    (h241 : p52 ∨ p59)
    (h242 : p52 ∨ p60)
    (h168 : p45 ∨ p47 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60)) : p52 ∨ p45 ∨ p47 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p52) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p45) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p47) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p56 := by
    rcases h238 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p57 := by
    rcases h239 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p58 := by
    rcases h240 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p59 := by
    rcases h241 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p60 := by
    rcases h242 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h168 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22128 (p45 p47 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 : Prop)
    (h143 : p45 ∨ p47 ∨ (¬ p51) ∨ (¬ p52) ∨ (¬ p53) ∨ (¬ p54) ∨ (¬ p55))
    (h233 : p51 ∨ p56)
    (h234 : p51 ∨ p57)
    (h235 : p51 ∨ p58)
    (h236 : p51 ∨ p59)
    (h237 : p51 ∨ p60)
    (h168 : p45 ∨ p47 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60)) : (¬ p52) ∨ p45 ∨ p47 ∨ (¬ p53) ∨ (¬ p54) ∨ (¬ p55) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p52 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p45) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p47) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p53 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p54 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p55 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p51) := by
    rcases h143 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u2 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u5)
  have u7 : p56 := by
    rcases h233 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p57 := by
    rcases h234 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p58 := by
    rcases h235 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p59 := by
    rcases h236 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p60 := by
    rcases h237 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h168 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22129 (p45 p47 p52 p53 p54 p55 : Prop)
    (h22124 : p55 ∨ p45 ∨ p47)
    (h22125 : p54 ∨ p45 ∨ p47)
    (h22126 : p53 ∨ p45 ∨ p47)
    (h22127 : p52 ∨ p45 ∨ p47)
    (h22128 : (¬ p52) ∨ p45 ∨ p47 ∨ (¬ p53) ∨ (¬ p54) ∨ (¬ p55)) : p45 ∨ p47 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p45) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p47) := fun hu => hn (Or.inr hu)
  have u2 : p55 := by
    rcases h22124 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p54 := by
    rcases h22125 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p53 := by
    rcases h22126 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p52 := by
    rcases h22127 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22128 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u2)

theorem step22130 (p41 p43 p51 p56 p57 p58 p59 p60 : Prop)
    (h233 : p51 ∨ p56)
    (h234 : p51 ∨ p57)
    (h235 : p51 ∨ p58)
    (h236 : p51 ∨ p59)
    (h237 : p51 ∨ p60)
    (h160 : p41 ∨ p43 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60)) : p51 ∨ p43 ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p51) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p43) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p56 := by
    rcases h233 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p57 := by
    rcases h234 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p58 := by
    rcases h235 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p59 := by
    rcases h236 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p60 := by
    rcases h237 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h160 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22131 (p41 p43 p55 p56 p57 p58 p59 p60 : Prop)
    (h253 : p55 ∨ p56)
    (h254 : p55 ∨ p57)
    (h255 : p55 ∨ p58)
    (h256 : p55 ∨ p59)
    (h257 : p55 ∨ p60)
    (h160 : p41 ∨ p43 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60)) : p55 ∨ p43 ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p55) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p43) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p56 := by
    rcases h253 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p57 := by
    rcases h254 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p58 := by
    rcases h255 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p59 := by
    rcases h256 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p60 := by
    rcases h257 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h160 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22132 (p41 p43 p54 p56 p57 p58 p59 p60 : Prop)
    (h248 : p54 ∨ p56)
    (h249 : p54 ∨ p57)
    (h250 : p54 ∨ p58)
    (h251 : p54 ∨ p59)
    (h252 : p54 ∨ p60)
    (h160 : p41 ∨ p43 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60)) : p54 ∨ p43 ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p54) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p43) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p56 := by
    rcases h248 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p57 := by
    rcases h249 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p58 := by
    rcases h250 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p59 := by
    rcases h251 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p60 := by
    rcases h252 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h160 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22133 (p41 p43 p53 p56 p57 p58 p59 p60 : Prop)
    (h243 : p53 ∨ p56)
    (h244 : p53 ∨ p57)
    (h245 : p53 ∨ p58)
    (h246 : p53 ∨ p59)
    (h247 : p53 ∨ p60)
    (h160 : p41 ∨ p43 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60)) : p53 ∨ p43 ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p53) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p43) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p56 := by
    rcases h243 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p57 := by
    rcases h244 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p58 := by
    rcases h245 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p59 := by
    rcases h246 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p60 := by
    rcases h247 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h160 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22134 (p41 p43 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 : Prop)
    (h135 : p41 ∨ p43 ∨ (¬ p51) ∨ (¬ p52) ∨ (¬ p53) ∨ (¬ p54) ∨ (¬ p55))
    (h238 : p52 ∨ p56)
    (h239 : p52 ∨ p57)
    (h240 : p52 ∨ p58)
    (h241 : p52 ∨ p59)
    (h242 : p52 ∨ p60)
    (h160 : p41 ∨ p43 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60)) : (¬ p53) ∨ p43 ∨ p41 ∨ (¬ p51) ∨ (¬ p55) ∨ (¬ p54) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p53 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p43) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p51 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p55 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p54 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p52) := by
    rcases h135 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u3)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u4)
  have u7 : p56 := by
    rcases h238 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p57 := by
    rcases h239 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p58 := by
    rcases h240 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p59 := by
    rcases h241 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p60 := by
    rcases h242 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h160 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22135 (p41 p43 p51 p53 p54 p55 : Prop)
    (h22130 : p51 ∨ p43 ∨ p41)
    (h22131 : p55 ∨ p43 ∨ p41)
    (h22132 : p54 ∨ p43 ∨ p41)
    (h22133 : p53 ∨ p43 ∨ p41)
    (h22134 : (¬ p53) ∨ p43 ∨ p41 ∨ (¬ p51) ∨ (¬ p55) ∨ (¬ p54)) : p43 ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p43) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p41) := fun hu => hn (Or.inr hu)
  have u2 : p51 := by
    rcases h22130 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p55 := by
    rcases h22131 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p54 := by
    rcases h22132 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p53 := by
    rcases h22133 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22134 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step22136 (p18 p41 p43 p45 p136 p140 p576 p581 : Prop)
    (h6739 : (¬ p41) ∨ (¬ p45))
    (h11334 : (¬ p45) ∨ (¬ p136) ∨ p576)
    (h22080 : p136 ∨ p140)
    (h16114 : (¬ p18) ∨ (¬ p43) ∨ (¬ p140) ∨ (¬ p581))
    (h22135 : p43 ∨ p41) : (¬ p45) ∨ p576 ∨ (¬ p581) ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p41) := by
    rcases h6739 with q0 | q1
    · exact q0
    · exact False.elim (q1 u0)
  have u5 : (¬ p136) := by
    rcases h11334 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (u1 q2)
  have u6 : p140 := by
    rcases h22080 with q0 | q1
    · exact False.elim (u5 q0)
    · exact q1
  have u7 : (¬ p43) := by
    rcases h16114 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u3)
    · exact q1
    · exact False.elim (q2 u6)
    · exact False.elim (q3 u2)
  rcases h22135 with q0 | q1
  · exact False.elim (u7 q0)
  · exact False.elim (u4 q1)

theorem step22137 (p256 p262 p273 p274 p275 p276 p277 p278 : Prop)
    (h1433 : p273 ∨ p274)
    (h1434 : p273 ∨ p275)
    (h1435 : p273 ∨ p276)
    (h1436 : p273 ∨ p277)
    (h1437 : p273 ∨ p278)
    (h1345 : p256 ∨ p262 ∨ (¬ p274) ∨ (¬ p275) ∨ (¬ p276) ∨ (¬ p277) ∨ (¬ p278)) : p273 ∨ p262 ∨ p256 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p273) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p262) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p256) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p274 := by
    rcases h1433 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p275 := by
    rcases h1434 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p276 := by
    rcases h1435 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p277 := by
    rcases h1436 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p278 := by
    rcases h1437 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1345 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22138 (p256 p262 p272 p274 p275 p276 p277 p278 : Prop)
    (h1428 : p272 ∨ p274)
    (h1429 : p272 ∨ p275)
    (h1430 : p272 ∨ p276)
    (h1431 : p272 ∨ p277)
    (h1432 : p272 ∨ p278)
    (h1345 : p256 ∨ p262 ∨ (¬ p274) ∨ (¬ p275) ∨ (¬ p276) ∨ (¬ p277) ∨ (¬ p278)) : p272 ∨ p262 ∨ p256 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p272) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p262) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p256) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p274 := by
    rcases h1428 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p275 := by
    rcases h1429 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p276 := by
    rcases h1430 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p277 := by
    rcases h1431 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p278 := by
    rcases h1432 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1345 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22139 (p256 p262 p271 p274 p275 p276 p277 p278 : Prop)
    (h1423 : p271 ∨ p274)
    (h1424 : p271 ∨ p275)
    (h1425 : p271 ∨ p276)
    (h1426 : p271 ∨ p277)
    (h1427 : p271 ∨ p278)
    (h1345 : p256 ∨ p262 ∨ (¬ p274) ∨ (¬ p275) ∨ (¬ p276) ∨ (¬ p277) ∨ (¬ p278)) : p271 ∨ p262 ∨ p256 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p271) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p262) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p256) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p274 := by
    rcases h1423 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p275 := by
    rcases h1424 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p276 := by
    rcases h1425 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p277 := by
    rcases h1426 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p278 := by
    rcases h1427 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1345 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22140 (p256 p262 p270 p274 p275 p276 p277 p278 : Prop)
    (h1418 : p270 ∨ p274)
    (h1419 : p270 ∨ p275)
    (h1420 : p270 ∨ p276)
    (h1421 : p270 ∨ p277)
    (h1422 : p270 ∨ p278)
    (h1345 : p256 ∨ p262 ∨ (¬ p274) ∨ (¬ p275) ∨ (¬ p276) ∨ (¬ p277) ∨ (¬ p278)) : p270 ∨ p262 ∨ p256 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p270) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p262) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p256) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p274 := by
    rcases h1418 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p275 := by
    rcases h1419 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p276 := by
    rcases h1420 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p277 := by
    rcases h1421 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p278 := by
    rcases h1422 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1345 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22141 (p256 p262 p269 p270 p271 p272 p273 p274 p275 p276 p277 p278 : Prop)
    (h1320 : p256 ∨ p262 ∨ (¬ p269) ∨ (¬ p270) ∨ (¬ p271) ∨ (¬ p272) ∨ (¬ p273))
    (h1413 : p269 ∨ p274)
    (h1414 : p269 ∨ p275)
    (h1415 : p269 ∨ p276)
    (h1416 : p269 ∨ p277)
    (h1417 : p269 ∨ p278)
    (h1345 : p256 ∨ p262 ∨ (¬ p274) ∨ (¬ p275) ∨ (¬ p276) ∨ (¬ p277) ∨ (¬ p278)) : (¬ p270) ∨ (¬ p273) ∨ p262 ∨ p256 ∨ (¬ p271) ∨ (¬ p272) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p270 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p262) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p256) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p271 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p272 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p269) := by
    rcases h1320 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p274 := by
    rcases h1413 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p275 := by
    rcases h1414 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p276 := by
    rcases h1415 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p277 := by
    rcases h1416 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p278 := by
    rcases h1417 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h1345 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22142 (p256 p262 p270 p271 p272 p273 : Prop)
    (h22137 : p273 ∨ p262 ∨ p256)
    (h22138 : p272 ∨ p262 ∨ p256)
    (h22139 : p271 ∨ p262 ∨ p256)
    (h22140 : p270 ∨ p262 ∨ p256)
    (h22141 : (¬ p270) ∨ (¬ p273) ∨ p262 ∨ p256 ∨ (¬ p271) ∨ (¬ p272)) : p262 ∨ p256 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p262) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p256) := fun hu => hn (Or.inr hu)
  have u2 : p273 := by
    rcases h22137 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p272 := by
    rcases h22138 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p271 := by
    rcases h22139 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p270 := by
    rcases h22140 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22141 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22145 (p137 p142 p148 p149 p150 p151 p152 p153 : Prop)
    (h776 : p148 ∨ p149)
    (h777 : p148 ∨ p150)
    (h778 : p148 ∨ p151)
    (h779 : p148 ∨ p152)
    (h780 : p148 ∨ p153)
    (h688 : p137 ∨ p142 ∨ (¬ p149) ∨ (¬ p150) ∨ (¬ p151) ∨ (¬ p152) ∨ (¬ p153)) : p148 ∨ p137 ∨ p142 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p148) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p137) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h688 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22146 (p137 p141 p144 p145 p146 p147 p148 p153 : Prop)
    (h760 : p144 ∨ p153)
    (h765 : p145 ∨ p153)
    (h770 : p146 ∨ p153)
    (h775 : p147 ∨ p153)
    (h662 : p137 ∨ p141 ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p147) ∨ (¬ p148)) : p153 ∨ (¬ p148) ∨ p137 ∨ p141 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p153) := fun hu => hn (Or.inl hu)
  have u1 : p148 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p137) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p141) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h662 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step22147 (p137 p141 p144 p145 p146 p147 p148 p152 : Prop)
    (h759 : p144 ∨ p152)
    (h764 : p145 ∨ p152)
    (h769 : p146 ∨ p152)
    (h774 : p147 ∨ p152)
    (h662 : p137 ∨ p141 ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p147) ∨ (¬ p148)) : p152 ∨ (¬ p148) ∨ p137 ∨ p141 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p152) := fun hu => hn (Or.inl hu)
  have u1 : p148 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p137) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p141) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p144 := by
    rcases h759 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p145 := by
    rcases h764 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p146 := by
    rcases h769 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p147 := by
    rcases h774 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h662 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step22148 (p137 p141 p144 p145 p146 p147 p148 p151 : Prop)
    (h758 : p144 ∨ p151)
    (h763 : p145 ∨ p151)
    (h768 : p146 ∨ p151)
    (h773 : p147 ∨ p151)
    (h662 : p137 ∨ p141 ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p147) ∨ (¬ p148)) : p151 ∨ (¬ p148) ∨ p137 ∨ p141 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p151) := fun hu => hn (Or.inl hu)
  have u1 : p148 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p137) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p141) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p144 := by
    rcases h758 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p145 := by
    rcases h763 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p146 := by
    rcases h768 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p147 := by
    rcases h773 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h662 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step22149 (p137 p141 p144 p145 p146 p147 p148 p150 : Prop)
    (h757 : p144 ∨ p150)
    (h762 : p145 ∨ p150)
    (h767 : p146 ∨ p150)
    (h772 : p147 ∨ p150)
    (h662 : p137 ∨ p141 ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p147) ∨ (¬ p148)) : p150 ∨ (¬ p148) ∨ p137 ∨ p141 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p150) := fun hu => hn (Or.inl hu)
  have u1 : p148 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p137) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p141) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p144 := by
    rcases h757 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p145 := by
    rcases h762 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p146 := by
    rcases h767 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p147 := by
    rcases h772 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h662 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step22150 (p137 p141 p142 p144 p145 p146 p147 p148 p149 p150 p151 p152 p153 : Prop)
    (h22145 : p148 ∨ p137 ∨ p142)
    (h22146 : p153 ∨ (¬ p148) ∨ p137 ∨ p141)
    (h22147 : p152 ∨ (¬ p148) ∨ p137 ∨ p141)
    (h22148 : p151 ∨ (¬ p148) ∨ p137 ∨ p141)
    (h22149 : p150 ∨ (¬ p148) ∨ p137 ∨ p141)
    (h688 : p137 ∨ p142 ∨ (¬ p149) ∨ (¬ p150) ∨ (¬ p151) ∨ (¬ p152) ∨ (¬ p153))
    (h756 : p144 ∨ p149)
    (h761 : p145 ∨ p149)
    (h766 : p146 ∨ p149)
    (h771 : p147 ∨ p149)
    (h662 : p137 ∨ p141 ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p147) ∨ (¬ p148)) : p137 ∨ p141 ∨ p142 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p137) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p141) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p142) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p148 := by
    rcases h22145 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u4 : p153 := by
    rcases h22146 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u0 q2)
    · exact False.elim (u1 q3)
  have u5 : p152 := by
    rcases h22147 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u0 q2)
    · exact False.elim (u1 q3)
  have u6 : p151 := by
    rcases h22148 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u0 q2)
    · exact False.elim (u1 q3)
  have u7 : p150 := by
    rcases h22149 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u0 q2)
    · exact False.elim (u1 q3)
  have u8 : (¬ p149) := by
    rcases h688 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u0 q0)
    · exact False.elim (u2 q1)
    · exact q2
    · exact False.elim (q3 u7)
    · exact False.elim (q4 u6)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u4)
  have u9 : p144 := by
    rcases h756 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u10 : p145 := by
    rcases h761 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u11 : p146 := by
    rcases h766 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u12 : p147 := by
    rcases h771 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h662 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u12)
  · exact False.elim (q6 u3)

theorem step22151 (p1074 p1311 p1318 p1319 p1320 p1321 p1322 p1323 : Prop)
    (h7960 : p1318 ∨ p1319)
    (h7961 : p1318 ∨ p1320)
    (h7962 : p1318 ∨ p1321)
    (h7963 : p1318 ∨ p1322)
    (h7964 : p1318 ∨ p1323)
    (h7876 : p1074 ∨ p1311 ∨ (¬ p1319) ∨ (¬ p1320) ∨ (¬ p1321) ∨ (¬ p1322) ∨ (¬ p1323)) : p1318 ∨ p1311 ∨ p1074 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1318) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1311) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1074) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1319 := by
    rcases h7960 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1320 := by
    rcases h7961 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1321 := by
    rcases h7962 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1322 := by
    rcases h7963 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1323 := by
    rcases h7964 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7876 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22152 (p1074 p1311 p1317 p1319 p1320 p1321 p1322 p1323 : Prop)
    (h7955 : p1317 ∨ p1319)
    (h7956 : p1317 ∨ p1320)
    (h7957 : p1317 ∨ p1321)
    (h7958 : p1317 ∨ p1322)
    (h7959 : p1317 ∨ p1323)
    (h7876 : p1074 ∨ p1311 ∨ (¬ p1319) ∨ (¬ p1320) ∨ (¬ p1321) ∨ (¬ p1322) ∨ (¬ p1323)) : p1317 ∨ p1311 ∨ p1074 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1317) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1311) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1074) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1319 := by
    rcases h7955 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1320 := by
    rcases h7956 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1321 := by
    rcases h7957 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1322 := by
    rcases h7958 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1323 := by
    rcases h7959 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7876 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22153 (p1074 p1311 p1316 p1319 p1320 p1321 p1322 p1323 : Prop)
    (h7950 : p1316 ∨ p1319)
    (h7951 : p1316 ∨ p1320)
    (h7952 : p1316 ∨ p1321)
    (h7953 : p1316 ∨ p1322)
    (h7954 : p1316 ∨ p1323)
    (h7876 : p1074 ∨ p1311 ∨ (¬ p1319) ∨ (¬ p1320) ∨ (¬ p1321) ∨ (¬ p1322) ∨ (¬ p1323)) : p1316 ∨ p1311 ∨ p1074 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1316) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1311) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1074) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1319 := by
    rcases h7950 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1320 := by
    rcases h7951 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1321 := by
    rcases h7952 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1322 := by
    rcases h7953 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1323 := by
    rcases h7954 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7876 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22154 (p1074 p1311 p1315 p1319 p1320 p1321 p1322 p1323 : Prop)
    (h7945 : p1315 ∨ p1319)
    (h7946 : p1315 ∨ p1320)
    (h7947 : p1315 ∨ p1321)
    (h7948 : p1315 ∨ p1322)
    (h7949 : p1315 ∨ p1323)
    (h7876 : p1074 ∨ p1311 ∨ (¬ p1319) ∨ (¬ p1320) ∨ (¬ p1321) ∨ (¬ p1322) ∨ (¬ p1323)) : p1315 ∨ p1311 ∨ p1074 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1315) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1311) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1074) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1319 := by
    rcases h7945 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1320 := by
    rcases h7946 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1321 := by
    rcases h7947 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1322 := by
    rcases h7948 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1323 := by
    rcases h7949 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7876 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22155 (p1074 p1311 p1314 p1315 p1316 p1317 p1318 p1319 p1320 p1321 p1322 p1323 : Prop)
    (h7851 : p1074 ∨ p1311 ∨ (¬ p1314) ∨ (¬ p1315) ∨ (¬ p1316) ∨ (¬ p1317) ∨ (¬ p1318))
    (h7940 : p1314 ∨ p1319)
    (h7941 : p1314 ∨ p1320)
    (h7942 : p1314 ∨ p1321)
    (h7943 : p1314 ∨ p1322)
    (h7944 : p1314 ∨ p1323)
    (h7876 : p1074 ∨ p1311 ∨ (¬ p1319) ∨ (¬ p1320) ∨ (¬ p1321) ∨ (¬ p1322) ∨ (¬ p1323)) : (¬ p1315) ∨ (¬ p1318) ∨ p1074 ∨ p1311 ∨ (¬ p1316) ∨ (¬ p1317) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1315 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1318 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1074) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1311) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1316 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1317 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1314) := by
    rcases h7851 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p1319 := by
    rcases h7940 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1320 := by
    rcases h7941 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1321 := by
    rcases h7942 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1322 := by
    rcases h7943 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1323 := by
    rcases h7944 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h7876 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22156 (p1074 p1311 p1315 p1316 p1317 p1318 : Prop)
    (h22151 : p1318 ∨ p1311 ∨ p1074)
    (h22152 : p1317 ∨ p1311 ∨ p1074)
    (h22153 : p1316 ∨ p1311 ∨ p1074)
    (h22154 : p1315 ∨ p1311 ∨ p1074)
    (h22155 : (¬ p1315) ∨ (¬ p1318) ∨ p1074 ∨ p1311 ∨ (¬ p1316) ∨ (¬ p1317)) : p1311 ∨ p1074 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1311) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1074) := fun hu => hn (Or.inr hu)
  have u2 : p1318 := by
    rcases h22151 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1317 := by
    rcases h22152 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1316 := by
    rcases h22153 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1315 := by
    rcases h22154 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22155 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22157 (p157 p1055 p1068 p1069 p1070 p1071 p1072 p1073 : Prop)
    (h6343 : p1068 ∨ p1069)
    (h6344 : p1068 ∨ p1070)
    (h6345 : p1068 ∨ p1071)
    (h6346 : p1068 ∨ p1072)
    (h6347 : p1068 ∨ p1073)
    (h6259 : p157 ∨ p1055 ∨ (¬ p1069) ∨ (¬ p1070) ∨ (¬ p1071) ∨ (¬ p1072) ∨ (¬ p1073)) : p1068 ∨ p157 ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1068) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p157) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1069 := by
    rcases h6343 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1070 := by
    rcases h6344 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1071 := by
    rcases h6345 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1072 := by
    rcases h6346 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1073 := by
    rcases h6347 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6259 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22158 (p157 p1055 p1067 p1069 p1070 p1071 p1072 p1073 : Prop)
    (h6338 : p1067 ∨ p1069)
    (h6339 : p1067 ∨ p1070)
    (h6340 : p1067 ∨ p1071)
    (h6341 : p1067 ∨ p1072)
    (h6342 : p1067 ∨ p1073)
    (h6259 : p157 ∨ p1055 ∨ (¬ p1069) ∨ (¬ p1070) ∨ (¬ p1071) ∨ (¬ p1072) ∨ (¬ p1073)) : p1067 ∨ p157 ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1067) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p157) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1069 := by
    rcases h6338 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1070 := by
    rcases h6339 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1071 := by
    rcases h6340 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1072 := by
    rcases h6341 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1073 := by
    rcases h6342 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6259 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22159 (p157 p1055 p1066 p1069 p1070 p1071 p1072 p1073 : Prop)
    (h6333 : p1066 ∨ p1069)
    (h6334 : p1066 ∨ p1070)
    (h6335 : p1066 ∨ p1071)
    (h6336 : p1066 ∨ p1072)
    (h6337 : p1066 ∨ p1073)
    (h6259 : p157 ∨ p1055 ∨ (¬ p1069) ∨ (¬ p1070) ∨ (¬ p1071) ∨ (¬ p1072) ∨ (¬ p1073)) : p1066 ∨ p157 ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1066) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p157) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1069 := by
    rcases h6333 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1070 := by
    rcases h6334 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1071 := by
    rcases h6335 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1072 := by
    rcases h6336 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1073 := by
    rcases h6337 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6259 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22160 (p157 p1055 p1065 p1069 p1070 p1071 p1072 p1073 : Prop)
    (h6328 : p1065 ∨ p1069)
    (h6329 : p1065 ∨ p1070)
    (h6330 : p1065 ∨ p1071)
    (h6331 : p1065 ∨ p1072)
    (h6332 : p1065 ∨ p1073)
    (h6259 : p157 ∨ p1055 ∨ (¬ p1069) ∨ (¬ p1070) ∨ (¬ p1071) ∨ (¬ p1072) ∨ (¬ p1073)) : p1065 ∨ p157 ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1065) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p157) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1069 := by
    rcases h6328 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1070 := by
    rcases h6329 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1071 := by
    rcases h6330 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1072 := by
    rcases h6331 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1073 := by
    rcases h6332 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6259 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22161 (p157 p1055 p1064 p1065 p1066 p1067 p1068 p1069 p1070 p1071 p1072 p1073 : Prop)
    (h6234 : p157 ∨ p1055 ∨ (¬ p1064) ∨ (¬ p1065) ∨ (¬ p1066) ∨ (¬ p1067) ∨ (¬ p1068))
    (h6323 : p1064 ∨ p1069)
    (h6324 : p1064 ∨ p1070)
    (h6325 : p1064 ∨ p1071)
    (h6326 : p1064 ∨ p1072)
    (h6327 : p1064 ∨ p1073)
    (h6259 : p157 ∨ p1055 ∨ (¬ p1069) ∨ (¬ p1070) ∨ (¬ p1071) ∨ (¬ p1072) ∨ (¬ p1073)) : (¬ p1065) ∨ (¬ p1068) ∨ p1055 ∨ p157 ∨ (¬ p1066) ∨ (¬ p1067) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1065 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1068 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p157) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1066 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1067 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1064) := by
    rcases h6234 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p1069 := by
    rcases h6323 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1070 := by
    rcases h6324 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1071 := by
    rcases h6325 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1072 := by
    rcases h6326 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1073 := by
    rcases h6327 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h6259 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22162 (p157 p1055 p1065 p1066 p1067 p1068 : Prop)
    (h22157 : p1068 ∨ p157 ∨ p1055)
    (h22158 : p1067 ∨ p157 ∨ p1055)
    (h22159 : p1066 ∨ p157 ∨ p1055)
    (h22160 : p1065 ∨ p157 ∨ p1055)
    (h22161 : (¬ p1065) ∨ (¬ p1068) ∨ p1055 ∨ p157 ∨ (¬ p1066) ∨ (¬ p1067)) : p157 ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p157) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr hu)
  have u2 : p1068 := by
    rcases h22157 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1067 := by
    rcases h22158 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1066 := by
    rcases h22159 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1065 := by
    rcases h22160 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22161 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22171 (p134 p142 p148 p149 p150 p151 p152 p153 : Prop)
    (h776 : p148 ∨ p149)
    (h777 : p148 ∨ p150)
    (h778 : p148 ∨ p151)
    (h779 : p148 ∨ p152)
    (h780 : p148 ∨ p153)
    (h693 : p134 ∨ p142 ∨ (¬ p149) ∨ (¬ p150) ∨ (¬ p151) ∨ (¬ p152) ∨ (¬ p153)) : p148 ∨ p142 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p148) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p142) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h693 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22172 (p134 p142 p144 p145 p146 p147 p148 p153 : Prop)
    (h22171 : p148 ∨ p142 ∨ p134)
    (h760 : p144 ∨ p153)
    (h765 : p145 ∨ p153)
    (h770 : p146 ∨ p153)
    (h775 : p147 ∨ p153)
    (h668 : p134 ∨ p142 ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p147) ∨ (¬ p148)) : p153 ∨ p142 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p153) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p142) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p148 := by
    rcases h22171 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
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
  rcases h668 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step22173 (p134 p142 p144 p145 p146 p147 p148 p152 : Prop)
    (h22171 : p148 ∨ p142 ∨ p134)
    (h759 : p144 ∨ p152)
    (h764 : p145 ∨ p152)
    (h769 : p146 ∨ p152)
    (h774 : p147 ∨ p152)
    (h668 : p134 ∨ p142 ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p147) ∨ (¬ p148)) : p152 ∨ p142 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p152) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p142) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p148 := by
    rcases h22171 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p144 := by
    rcases h759 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p145 := by
    rcases h764 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p146 := by
    rcases h769 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p147 := by
    rcases h774 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h668 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step22174 (p134 p142 p144 p145 p146 p147 p148 p151 : Prop)
    (h22171 : p148 ∨ p142 ∨ p134)
    (h758 : p144 ∨ p151)
    (h763 : p145 ∨ p151)
    (h768 : p146 ∨ p151)
    (h773 : p147 ∨ p151)
    (h668 : p134 ∨ p142 ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p147) ∨ (¬ p148)) : p151 ∨ p142 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p151) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p142) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p148 := by
    rcases h22171 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p144 := by
    rcases h758 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p145 := by
    rcases h763 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p146 := by
    rcases h768 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p147 := by
    rcases h773 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h668 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step22175 (p134 p142 p144 p145 p146 p147 p148 p150 : Prop)
    (h22171 : p148 ∨ p142 ∨ p134)
    (h757 : p144 ∨ p150)
    (h762 : p145 ∨ p150)
    (h767 : p146 ∨ p150)
    (h772 : p147 ∨ p150)
    (h668 : p134 ∨ p142 ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p147) ∨ (¬ p148)) : p150 ∨ p142 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p150) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p142) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p148 := by
    rcases h22171 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p144 := by
    rcases h757 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p145 := by
    rcases h762 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p146 := by
    rcases h767 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p147 := by
    rcases h772 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h668 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step22176 (p134 p142 p144 p145 p146 p147 p148 p149 p150 p151 p152 p153 : Prop)
    (h22171 : p148 ∨ p142 ∨ p134)
    (h22172 : p153 ∨ p142 ∨ p134)
    (h22173 : p152 ∨ p142 ∨ p134)
    (h22174 : p151 ∨ p142 ∨ p134)
    (h22175 : p150 ∨ p142 ∨ p134)
    (h693 : p134 ∨ p142 ∨ (¬ p149) ∨ (¬ p150) ∨ (¬ p151) ∨ (¬ p152) ∨ (¬ p153))
    (h756 : p144 ∨ p149)
    (h761 : p145 ∨ p149)
    (h766 : p146 ∨ p149)
    (h771 : p147 ∨ p149)
    (h668 : p134 ∨ p142 ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p147) ∨ (¬ p148)) : p142 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p142) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p134) := fun hu => hn (Or.inr hu)
  have u2 : p148 := by
    rcases h22171 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p153 := by
    rcases h22172 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p152 := by
    rcases h22173 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p151 := by
    rcases h22174 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p150 := by
    rcases h22175 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p149) := by
    rcases h693 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact q2
    · exact False.elim (q3 u6)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u3)
  have u8 : p144 := by
    rcases h756 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p145 := by
    rcases h761 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p146 := by
    rcases h766 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p147 := by
    rcases h771 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h668 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u2)

theorem step22177 (p18 p45 p576 p581 : Prop)
    (h21688 : p576 ∨ p581)
    (h22136 : (¬ p45) ∨ p576 ∨ (¬ p581) ∨ (¬ p18)) : p576 ∨ (¬ p45) ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p576) := fun hu => hn (Or.inl hu)
  have u1 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p581 := by
    rcases h21688 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h22136 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)

theorem step22178 (p191 p192 p200 p201 p202 p203 p204 p205 : Prop)
    (h1042 : p200 ∨ p201)
    (h1043 : p200 ∨ p202)
    (h1044 : p200 ∨ p203)
    (h1045 : p200 ∨ p204)
    (h1046 : p200 ∨ p205)
    (h967 : p191 ∨ p192 ∨ (¬ p201) ∨ (¬ p202) ∨ (¬ p203) ∨ (¬ p204) ∨ (¬ p205)) : p200 ∨ p191 ∨ p192 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p200) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p191) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p192) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p201 := by
    rcases h1042 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p202 := by
    rcases h1043 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p203 := by
    rcases h1044 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p204 := by
    rcases h1045 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p205 := by
    rcases h1046 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h967 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22179 (p191 p192 p199 p201 p202 p203 p204 p205 : Prop)
    (h1037 : p199 ∨ p201)
    (h1038 : p199 ∨ p202)
    (h1039 : p199 ∨ p203)
    (h1040 : p199 ∨ p204)
    (h1041 : p199 ∨ p205)
    (h967 : p191 ∨ p192 ∨ (¬ p201) ∨ (¬ p202) ∨ (¬ p203) ∨ (¬ p204) ∨ (¬ p205)) : p199 ∨ p191 ∨ p192 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p199) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p191) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p192) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h967 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22180 (p191 p192 p198 p201 p202 p203 p204 p205 : Prop)
    (h1032 : p198 ∨ p201)
    (h1033 : p198 ∨ p202)
    (h1034 : p198 ∨ p203)
    (h1035 : p198 ∨ p204)
    (h1036 : p198 ∨ p205)
    (h967 : p191 ∨ p192 ∨ (¬ p201) ∨ (¬ p202) ∨ (¬ p203) ∨ (¬ p204) ∨ (¬ p205)) : p198 ∨ p191 ∨ p192 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p198) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p191) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p192) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h967 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22181 (p191 p192 p197 p201 p202 p203 p204 p205 : Prop)
    (h1027 : p197 ∨ p201)
    (h1028 : p197 ∨ p202)
    (h1029 : p197 ∨ p203)
    (h1030 : p197 ∨ p204)
    (h1031 : p197 ∨ p205)
    (h967 : p191 ∨ p192 ∨ (¬ p201) ∨ (¬ p202) ∨ (¬ p203) ∨ (¬ p204) ∨ (¬ p205)) : p197 ∨ p191 ∨ p192 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p197) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p191) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p192) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h967 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22182 (p191 p192 p196 p197 p198 p199 p200 p201 p202 p203 p204 p205 : Prop)
    (h942 : p191 ∨ p192 ∨ (¬ p196) ∨ (¬ p197) ∨ (¬ p198) ∨ (¬ p199) ∨ (¬ p200))
    (h1022 : p196 ∨ p201)
    (h1023 : p196 ∨ p202)
    (h1024 : p196 ∨ p203)
    (h1025 : p196 ∨ p204)
    (h1026 : p196 ∨ p205)
    (h967 : p191 ∨ p192 ∨ (¬ p201) ∨ (¬ p202) ∨ (¬ p203) ∨ (¬ p204) ∨ (¬ p205)) : (¬ p197) ∨ (¬ p200) ∨ p192 ∨ p191 ∨ (¬ p198) ∨ (¬ p199) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p197 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p200 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p192) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p191) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p198 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p199 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p196) := by
    rcases h942 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p201 := by
    rcases h1022 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p202 := by
    rcases h1023 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p203 := by
    rcases h1024 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p204 := by
    rcases h1025 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p205 := by
    rcases h1026 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h967 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22183 (p191 p192 p197 p198 p199 p200 : Prop)
    (h22178 : p200 ∨ p191 ∨ p192)
    (h22179 : p199 ∨ p191 ∨ p192)
    (h22180 : p198 ∨ p191 ∨ p192)
    (h22181 : p197 ∨ p191 ∨ p192)
    (h22182 : (¬ p197) ∨ (¬ p200) ∨ p192 ∨ p191 ∨ (¬ p198) ∨ (¬ p199)) : p191 ∨ p192 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p191) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p192) := fun hu => hn (Or.inr hu)
  have u2 : p200 := by
    rcases h22178 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p199 := by
    rcases h22179 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p198 := by
    rcases h22180 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p197 := by
    rcases h22181 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22182 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22184 (p423 p1142 p1153 p1154 p1155 p1156 p1157 p1158 : Prop)
    (h6884 : p1153 ∨ p1154)
    (h6885 : p1153 ∨ p1155)
    (h6886 : p1153 ∨ p1156)
    (h6887 : p1153 ∨ p1157)
    (h6888 : p1153 ∨ p1158)
    (h6796 : p423 ∨ p1142 ∨ (¬ p1154) ∨ (¬ p1155) ∨ (¬ p1156) ∨ (¬ p1157) ∨ (¬ p1158)) : p1153 ∨ p1142 ∨ p423 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1153) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1142) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p423) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1154 := by
    rcases h6884 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1155 := by
    rcases h6885 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1156 := by
    rcases h6886 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1157 := by
    rcases h6887 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1158 := by
    rcases h6888 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6796 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22185 (p423 p1142 p1152 p1154 p1155 p1156 p1157 p1158 : Prop)
    (h6879 : p1152 ∨ p1154)
    (h6880 : p1152 ∨ p1155)
    (h6881 : p1152 ∨ p1156)
    (h6882 : p1152 ∨ p1157)
    (h6883 : p1152 ∨ p1158)
    (h6796 : p423 ∨ p1142 ∨ (¬ p1154) ∨ (¬ p1155) ∨ (¬ p1156) ∨ (¬ p1157) ∨ (¬ p1158)) : p1152 ∨ p1142 ∨ p423 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1152) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1142) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p423) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1154 := by
    rcases h6879 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1155 := by
    rcases h6880 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1156 := by
    rcases h6881 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1157 := by
    rcases h6882 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1158 := by
    rcases h6883 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6796 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22186 (p423 p1142 p1151 p1154 p1155 p1156 p1157 p1158 : Prop)
    (h6874 : p1151 ∨ p1154)
    (h6875 : p1151 ∨ p1155)
    (h6876 : p1151 ∨ p1156)
    (h6877 : p1151 ∨ p1157)
    (h6878 : p1151 ∨ p1158)
    (h6796 : p423 ∨ p1142 ∨ (¬ p1154) ∨ (¬ p1155) ∨ (¬ p1156) ∨ (¬ p1157) ∨ (¬ p1158)) : p1151 ∨ p1142 ∨ p423 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1151) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1142) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p423) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1154 := by
    rcases h6874 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1155 := by
    rcases h6875 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1156 := by
    rcases h6876 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1157 := by
    rcases h6877 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1158 := by
    rcases h6878 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6796 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22187 (p423 p1142 p1150 p1154 p1155 p1156 p1157 p1158 : Prop)
    (h6869 : p1150 ∨ p1154)
    (h6870 : p1150 ∨ p1155)
    (h6871 : p1150 ∨ p1156)
    (h6872 : p1150 ∨ p1157)
    (h6873 : p1150 ∨ p1158)
    (h6796 : p423 ∨ p1142 ∨ (¬ p1154) ∨ (¬ p1155) ∨ (¬ p1156) ∨ (¬ p1157) ∨ (¬ p1158)) : p1150 ∨ p1142 ∨ p423 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1150) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1142) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p423) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1154 := by
    rcases h6869 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1155 := by
    rcases h6870 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1156 := by
    rcases h6871 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1157 := by
    rcases h6872 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1158 := by
    rcases h6873 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6796 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22188 (p423 p1142 p1149 p1150 p1151 p1152 p1153 p1154 p1155 p1156 p1157 p1158 : Prop)
    (h6771 : p423 ∨ p1142 ∨ (¬ p1149) ∨ (¬ p1150) ∨ (¬ p1151) ∨ (¬ p1152) ∨ (¬ p1153))
    (h6864 : p1149 ∨ p1154)
    (h6865 : p1149 ∨ p1155)
    (h6866 : p1149 ∨ p1156)
    (h6867 : p1149 ∨ p1157)
    (h6868 : p1149 ∨ p1158)
    (h6796 : p423 ∨ p1142 ∨ (¬ p1154) ∨ (¬ p1155) ∨ (¬ p1156) ∨ (¬ p1157) ∨ (¬ p1158)) : (¬ p1150) ∨ (¬ p1153) ∨ p423 ∨ p1142 ∨ (¬ p1151) ∨ (¬ p1152) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1150 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1153 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p423) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1142) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1151 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1152 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1149) := by
    rcases h6771 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p1154 := by
    rcases h6864 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1155 := by
    rcases h6865 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1156 := by
    rcases h6866 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1157 := by
    rcases h6867 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1158 := by
    rcases h6868 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h6796 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22189 (p423 p1142 p1150 p1151 p1152 p1153 : Prop)
    (h22184 : p1153 ∨ p1142 ∨ p423)
    (h22185 : p1152 ∨ p1142 ∨ p423)
    (h22186 : p1151 ∨ p1142 ∨ p423)
    (h22187 : p1150 ∨ p1142 ∨ p423)
    (h22188 : (¬ p1150) ∨ (¬ p1153) ∨ p423 ∨ p1142 ∨ (¬ p1151) ∨ (¬ p1152)) : p1142 ∨ p423 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1142) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p423) := fun hu => hn (Or.inr hu)
  have u2 : p1153 := by
    rcases h22184 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1152 := by
    rcases h22185 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1151 := by
    rcases h22186 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1150 := by
    rcases h22187 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22188 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22190 (p41 p46 p52 p56 p57 p58 p59 p60 : Prop)
    (h238 : p52 ∨ p56)
    (h239 : p52 ∨ p57)
    (h240 : p52 ∨ p58)
    (h241 : p52 ∨ p59)
    (h242 : p52 ∨ p60)
    (h180 : p41 ∨ p46 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60)) : p52 ∨ p46 ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p52) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p46) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p56 := by
    rcases h238 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p57 := by
    rcases h239 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p58 := by
    rcases h240 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p59 := by
    rcases h241 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p60 := by
    rcases h242 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h180 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22191 (p41 p46 p51 p56 p57 p58 p59 p60 : Prop)
    (h233 : p51 ∨ p56)
    (h234 : p51 ∨ p57)
    (h235 : p51 ∨ p58)
    (h236 : p51 ∨ p59)
    (h237 : p51 ∨ p60)
    (h180 : p41 ∨ p46 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60)) : p51 ∨ p46 ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p51) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p46) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p56 := by
    rcases h233 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p57 := by
    rcases h234 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p58 := by
    rcases h235 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p59 := by
    rcases h236 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p60 := by
    rcases h237 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h180 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22192 (p41 p46 p55 p56 p57 p58 p59 p60 : Prop)
    (h253 : p55 ∨ p56)
    (h254 : p55 ∨ p57)
    (h255 : p55 ∨ p58)
    (h256 : p55 ∨ p59)
    (h257 : p55 ∨ p60)
    (h180 : p41 ∨ p46 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60)) : p55 ∨ p46 ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p55) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p46) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p56 := by
    rcases h253 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p57 := by
    rcases h254 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p58 := by
    rcases h255 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p59 := by
    rcases h256 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p60 := by
    rcases h257 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h180 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22193 (p41 p46 p54 p56 p57 p58 p59 p60 : Prop)
    (h248 : p54 ∨ p56)
    (h249 : p54 ∨ p57)
    (h250 : p54 ∨ p58)
    (h251 : p54 ∨ p59)
    (h252 : p54 ∨ p60)
    (h180 : p41 ∨ p46 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60)) : p54 ∨ p46 ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p54) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p46) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p56 := by
    rcases h248 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p57 := by
    rcases h249 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p58 := by
    rcases h250 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p59 := by
    rcases h251 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p60 := by
    rcases h252 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h180 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22194 (p41 p46 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 : Prop)
    (h155 : p41 ∨ p46 ∨ (¬ p51) ∨ (¬ p52) ∨ (¬ p53) ∨ (¬ p54) ∨ (¬ p55))
    (h243 : p53 ∨ p56)
    (h244 : p53 ∨ p57)
    (h245 : p53 ∨ p58)
    (h246 : p53 ∨ p59)
    (h247 : p53 ∨ p60)
    (h180 : p41 ∨ p46 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60)) : (¬ p54) ∨ (¬ p55) ∨ p41 ∨ (¬ p52) ∨ (¬ p51) ∨ p46 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p54 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p55 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p52 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p51 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p46) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p53) := by
    rcases h155 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u5 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u3)
    · exact q4
    · exact False.elim (q5 u0)
    · exact False.elim (q6 u1)
  have u7 : p56 := by
    rcases h243 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p57 := by
    rcases h244 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p58 := by
    rcases h245 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p59 := by
    rcases h246 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p60 := by
    rcases h247 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h180 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22195 (p41 p46 p51 p52 p54 p55 : Prop)
    (h22190 : p52 ∨ p46 ∨ p41)
    (h22191 : p51 ∨ p46 ∨ p41)
    (h22192 : p55 ∨ p46 ∨ p41)
    (h22193 : p54 ∨ p46 ∨ p41)
    (h22194 : (¬ p54) ∨ (¬ p55) ∨ p41 ∨ (¬ p52) ∨ (¬ p51) ∨ p46) : p46 ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p46) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p41) := fun hu => hn (Or.inr hu)
  have u2 : p52 := by
    rcases h22190 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p51 := by
    rcases h22191 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p55 := by
    rcases h22192 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p54 := by
    rcases h22193 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22194 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u0 q5)

theorem step22196 (p235 p423 p1149 p1154 p1155 p1156 p1157 p1158 : Prop)
    (h6864 : p1149 ∨ p1154)
    (h6865 : p1149 ∨ p1155)
    (h6866 : p1149 ∨ p1156)
    (h6867 : p1149 ∨ p1157)
    (h6868 : p1149 ∨ p1158)
    (h6791 : p235 ∨ p423 ∨ (¬ p1154) ∨ (¬ p1155) ∨ (¬ p1156) ∨ (¬ p1157) ∨ (¬ p1158)) : p1149 ∨ p235 ∨ p423 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1149) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p235) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p423) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1154 := by
    rcases h6864 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1155 := by
    rcases h6865 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1156 := by
    rcases h6866 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1157 := by
    rcases h6867 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1158 := by
    rcases h6868 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6791 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22197 (p235 p423 p1153 p1154 p1155 p1156 p1157 p1158 : Prop)
    (h6884 : p1153 ∨ p1154)
    (h6885 : p1153 ∨ p1155)
    (h6886 : p1153 ∨ p1156)
    (h6887 : p1153 ∨ p1157)
    (h6888 : p1153 ∨ p1158)
    (h6791 : p235 ∨ p423 ∨ (¬ p1154) ∨ (¬ p1155) ∨ (¬ p1156) ∨ (¬ p1157) ∨ (¬ p1158)) : p1153 ∨ p235 ∨ p423 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1153) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p235) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p423) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1154 := by
    rcases h6884 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1155 := by
    rcases h6885 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1156 := by
    rcases h6886 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1157 := by
    rcases h6887 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1158 := by
    rcases h6888 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6791 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22198 (p235 p423 p1152 p1154 p1155 p1156 p1157 p1158 : Prop)
    (h6879 : p1152 ∨ p1154)
    (h6880 : p1152 ∨ p1155)
    (h6881 : p1152 ∨ p1156)
    (h6882 : p1152 ∨ p1157)
    (h6883 : p1152 ∨ p1158)
    (h6791 : p235 ∨ p423 ∨ (¬ p1154) ∨ (¬ p1155) ∨ (¬ p1156) ∨ (¬ p1157) ∨ (¬ p1158)) : p1152 ∨ p235 ∨ p423 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1152) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p235) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p423) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1154 := by
    rcases h6879 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1155 := by
    rcases h6880 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1156 := by
    rcases h6881 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1157 := by
    rcases h6882 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1158 := by
    rcases h6883 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6791 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22199 (p235 p423 p1151 p1154 p1155 p1156 p1157 p1158 : Prop)
    (h6874 : p1151 ∨ p1154)
    (h6875 : p1151 ∨ p1155)
    (h6876 : p1151 ∨ p1156)
    (h6877 : p1151 ∨ p1157)
    (h6878 : p1151 ∨ p1158)
    (h6791 : p235 ∨ p423 ∨ (¬ p1154) ∨ (¬ p1155) ∨ (¬ p1156) ∨ (¬ p1157) ∨ (¬ p1158)) : p1151 ∨ p235 ∨ p423 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1151) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p235) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p423) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1154 := by
    rcases h6874 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1155 := by
    rcases h6875 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1156 := by
    rcases h6876 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1157 := by
    rcases h6877 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1158 := by
    rcases h6878 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6791 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22201 (p69 p86 p435 p814 p856 p861 p1187 p1333 p1335 p1346 p1489 p1508 : Prop)
    (h18722 : (¬ p69) ∨ (¬ p86) ∨ (¬ p435) ∨ (¬ p1187) ∨ (¬ p1335) ∨ (¬ p1346) ∨ (¬ p1508))
    (h13653 : (¬ p814) ∨ (¬ p856) ∨ (¬ p1346))
    (h21548 : p1508 ∨ p1489)
    (h20979 : p856 ∨ p861)
    (h10842 : (¬ p861) ∨ (¬ p1333) ∨ (¬ p1489)) : (¬ p1346) ∨ (¬ p814) ∨ (¬ p435) ∨ (¬ p1335) ∨ (¬ p1333) ∨ (¬ p86) ∨ (¬ p1187) ∨ (¬ p69) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p1508) := by
    rcases h18722 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u7)
    · exact False.elim (q1 u5)
    · exact False.elim (q2 u2)
    · exact False.elim (q3 u6)
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u0)
    · exact q6
  have u9 : (¬ p856) := by
    rcases h13653 with q0 | q1 | q2
    · exact False.elim (q0 u1)
    · exact q1
    · exact False.elim (q2 u0)
  have u10 : p1489 := by
    rcases h21548 with q0 | q1
    · exact False.elim (u8 q0)
    · exact q1
  have u11 : p861 := by
    rcases h20979 with q0 | q1
    · exact False.elim (u9 q0)
    · exact q1
  rcases h10842 with q0 | q1 | q2
  · exact False.elim (q0 u11)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u10)

theorem step22203 (p1118 p1122 p1125 p1126 p1127 p1128 p1129 p1130 p1131 p1132 p1133 p1134 : Prop)
    (h6639 : p1118 ∨ p1122 ∨ (¬ p1130) ∨ (¬ p1131) ∨ (¬ p1132) ∨ (¬ p1133) ∨ (¬ p1134))
    (h6708 : p1125 ∨ p1130)
    (h6713 : p1126 ∨ p1130)
    (h6718 : p1127 ∨ p1130)
    (h6723 : p1128 ∨ p1130)
    (h6728 : p1129 ∨ p1130)
    (h6614 : p1118 ∨ p1122 ∨ (¬ p1125) ∨ (¬ p1126) ∨ (¬ p1127) ∨ (¬ p1128) ∨ (¬ p1129)) : (¬ p1134) ∨ (¬ p1133) ∨ p1122 ∨ (¬ p1131) ∨ p1118 ∨ (¬ p1132) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1133 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1122) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1131 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1118) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1132 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1130) := by
    rcases h6639 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u4 q0)
    · exact False.elim (u2 q1)
    · exact q2
    · exact False.elim (q3 u3)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u1)
    · exact False.elim (q6 u0)
  have u7 : p1125 := by
    rcases h6708 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1126 := by
    rcases h6713 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1127 := by
    rcases h6718 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1128 := by
    rcases h6723 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1129 := by
    rcases h6728 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h6614 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22204 (p1118 p1122 p1131 p1132 p1133 p1134 : Prop)
    (h22118 : p1134 ∨ p1122 ∨ p1118)
    (h22119 : p1133 ∨ p1122 ∨ p1118)
    (h22120 : p1132 ∨ p1122 ∨ p1118)
    (h22121 : p1131 ∨ p1122 ∨ p1118)
    (h22203 : (¬ p1134) ∨ (¬ p1133) ∨ p1122 ∨ (¬ p1131) ∨ p1118 ∨ (¬ p1132)) : p1122 ∨ p1118 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1122) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1118) := fun hu => hn (Or.inr hu)
  have u2 : p1134 := by
    rcases h22118 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1133 := by
    rcases h22119 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1132 := by
    rcases h22120 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1131 := by
    rcases h22121 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22203 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u5)
  · exact False.elim (u1 q4)
  · exact False.elim (q5 u4)

theorem step22206 (p63 p85 p91 p96 p97 p98 p99 p100 : Prop)
    (h494 : p91 ∨ p96)
    (h495 : p91 ∨ p97)
    (h496 : p91 ∨ p98)
    (h497 : p91 ∨ p99)
    (h498 : p91 ∨ p100)
    (h431 : p63 ∨ p85 ∨ (¬ p96) ∨ (¬ p97) ∨ (¬ p98) ∨ (¬ p99) ∨ (¬ p100)) : p91 ∨ p85 ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p91) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p85) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p96 := by
    rcases h494 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p97 := by
    rcases h495 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p98 := by
    rcases h496 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p99 := by
    rcases h497 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p100 := by
    rcases h498 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h431 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22207 (p63 p85 p95 p96 p97 p98 p99 p100 : Prop)
    (h514 : p95 ∨ p96)
    (h515 : p95 ∨ p97)
    (h516 : p95 ∨ p98)
    (h517 : p95 ∨ p99)
    (h518 : p95 ∨ p100)
    (h431 : p63 ∨ p85 ∨ (¬ p96) ∨ (¬ p97) ∨ (¬ p98) ∨ (¬ p99) ∨ (¬ p100)) : p95 ∨ p85 ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p95) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p85) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p96 := by
    rcases h514 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p97 := by
    rcases h515 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p98 := by
    rcases h516 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p99 := by
    rcases h517 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p100 := by
    rcases h518 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h431 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22208 (p63 p85 p94 p96 p97 p98 p99 p100 : Prop)
    (h509 : p94 ∨ p96)
    (h510 : p94 ∨ p97)
    (h511 : p94 ∨ p98)
    (h512 : p94 ∨ p99)
    (h513 : p94 ∨ p100)
    (h431 : p63 ∨ p85 ∨ (¬ p96) ∨ (¬ p97) ∨ (¬ p98) ∨ (¬ p99) ∨ (¬ p100)) : p94 ∨ p85 ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p94) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p85) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p96 := by
    rcases h509 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p97 := by
    rcases h510 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p98 := by
    rcases h511 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p99 := by
    rcases h512 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p100 := by
    rcases h513 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h431 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22209 (p63 p85 p93 p96 p97 p98 p99 p100 : Prop)
    (h504 : p93 ∨ p96)
    (h505 : p93 ∨ p97)
    (h506 : p93 ∨ p98)
    (h507 : p93 ∨ p99)
    (h508 : p93 ∨ p100)
    (h431 : p63 ∨ p85 ∨ (¬ p96) ∨ (¬ p97) ∨ (¬ p98) ∨ (¬ p99) ∨ (¬ p100)) : p93 ∨ p85 ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p93) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p85) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p96 := by
    rcases h504 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p97 := by
    rcases h505 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p98 := by
    rcases h506 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p99 := by
    rcases h507 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p100 := by
    rcases h508 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h431 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22210 (p63 p85 p92 p96 p97 p98 p99 p100 : Prop)
    (h499 : p92 ∨ p96)
    (h500 : p92 ∨ p97)
    (h501 : p92 ∨ p98)
    (h502 : p92 ∨ p99)
    (h503 : p92 ∨ p100)
    (h431 : p63 ∨ p85 ∨ (¬ p96) ∨ (¬ p97) ∨ (¬ p98) ∨ (¬ p99) ∨ (¬ p100)) : p92 ∨ p85 ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p92) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p85) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p96 := by
    rcases h499 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p97 := by
    rcases h500 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p98 := by
    rcases h501 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p99 := by
    rcases h502 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p100 := by
    rcases h503 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h431 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22211 (p63 p85 p91 p92 p93 p94 p95 : Prop)
    (h22206 : p91 ∨ p85 ∨ p63)
    (h22207 : p95 ∨ p85 ∨ p63)
    (h22208 : p94 ∨ p85 ∨ p63)
    (h22209 : p93 ∨ p85 ∨ p63)
    (h22210 : p92 ∨ p85 ∨ p63)
    (h406 : p63 ∨ p85 ∨ (¬ p91) ∨ (¬ p92) ∨ (¬ p93) ∨ (¬ p94) ∨ (¬ p95)) : p85 ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p85) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p63) := fun hu => hn (Or.inr hu)
  have u2 : p91 := by
    rcases h22206 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p95 := by
    rcases h22207 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p94 := by
    rcases h22208 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p93 := by
    rcases h22209 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p92 := by
    rcases h22210 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h406 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u3)

theorem step22213 (p10 p126 p139 p140 p301 p303 p323 p329 p996 : Prop)
    (h21681 : p323 ∨ p10)
    (h21610 : p329 ∨ p10)
    (h20973 : p301 ∨ p126)
    (h14549 : p126 ∨ (¬ p140) ∨ (¬ p323))
    (h17948 : (¬ p139) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p329) ∨ (¬ p996))
    (h21822 : p139 ∨ p140) : p126 ∨ (¬ p303) ∨ (¬ p996) ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p323 := by
    rcases h21681 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u5 : p329 := by
    rcases h21610 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p301 := by
    rcases h20973 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : (¬ p140) := by
    rcases h14549 with q0 | q1 | q2
    · exact False.elim (u0 q0)
    · exact q1
    · exact False.elim (q2 u4)
  have u8 : (¬ p139) := by
    rcases h17948 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u6)
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u2)
  rcases h21822 with q0 | q1
  · exact False.elim (u8 q0)
  · exact False.elim (u7 q1)

theorem step22216 (p833 p834 p843 p844 p845 p846 p847 p848 p849 p850 p851 p852 : Prop)
    (h4795 : p833 ∨ p834 ∨ (¬ p843) ∨ (¬ p844) ∨ (¬ p845) ∨ (¬ p846) ∨ (¬ p847))
    (h4895 : p843 ∨ p848)
    (h4896 : p843 ∨ p849)
    (h4897 : p843 ∨ p850)
    (h4898 : p843 ∨ p851)
    (h4899 : p843 ∨ p852)
    (h4820 : p833 ∨ p834 ∨ (¬ p848) ∨ (¬ p849) ∨ (¬ p850) ∨ (¬ p851) ∨ (¬ p852)) : p833 ∨ (¬ p847) ∨ p834 ∨ (¬ p845) ∨ (¬ p846) ∨ (¬ p844) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p833) := fun hu => hn (Or.inl hu)
  have u1 : p847 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p834) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p845 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p846 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p844 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p843) := by
    rcases h4795 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u0 q0)
    · exact False.elim (u2 q1)
    · exact q2
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u1)
  have u7 : p848 := by
    rcases h4895 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p849 := by
    rcases h4896 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p850 := by
    rcases h4897 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p851 := by
    rcases h4898 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p852 := by
    rcases h4899 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h4820 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22217 (p833 p834 p844 p845 p846 p847 : Prop)
    (h21978 : p847 ∨ p834 ∨ p833)
    (h21979 : p846 ∨ p834 ∨ p833)
    (h21980 : p845 ∨ p834 ∨ p833)
    (h21981 : p844 ∨ p834 ∨ p833)
    (h22216 : p833 ∨ (¬ p847) ∨ p834 ∨ (¬ p845) ∨ (¬ p846) ∨ (¬ p844)) : p834 ∨ p833 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p834) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p833) := fun hu => hn (Or.inr hu)
  have u2 : p847 := by
    rcases h21978 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p846 := by
    rcases h21979 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p845 := by
    rcases h21980 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p844 := by
    rcases h21981 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22216 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)

theorem step22218 (p101 p121 p156 p185 p192 p206 p657 p790 p833 p834 p961 : Prop)
    (h11556 : (¬ p185) ∨ (¬ p790) ∨ (¬ p834))
    (h19996 : (¬ p101) ∨ (¬ p121) ∨ (¬ p156) ∨ (¬ p185) ∨ (¬ p192) ∨ (¬ p206) ∨ (¬ p657) ∨ (¬ p790) ∨ (¬ p833) ∨ (¬ p961))
    (h22217 : p834 ∨ p833) : (¬ p790) ∨ (¬ p961) ∨ (¬ p156) ∨ (¬ p192) ∨ (¬ p121) ∨ (¬ p657) ∨ (¬ p185) ∨ (¬ p101) ∨ (¬ p206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p834) := by
    rcases h11556 with q0 | q1 | q2
    · exact False.elim (q0 u6)
    · exact False.elim (q1 u0)
    · exact q2
  have u10 : (¬ p833) := by
    rcases h19996 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
    · exact False.elim (q0 u7)
    · exact False.elim (q1 u4)
    · exact False.elim (q2 u2)
    · exact False.elim (q3 u6)
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u8)
    · exact False.elim (q6 u5)
    · exact False.elim (q7 u0)
    · exact q8
    · exact False.elim (q9 u1)
  rcases h22217 with q0 | q1
  · exact False.elim (u9 q0)
  · exact False.elim (u10 q1)

theorem step22219 (p515 p519 p526 p527 p528 p529 p530 p531 : Prop)
    (h2979 : p526 ∨ p527)
    (h2980 : p526 ∨ p528)
    (h2981 : p526 ∨ p529)
    (h2982 : p526 ∨ p530)
    (h2983 : p526 ∨ p531)
    (h2890 : p515 ∨ p519 ∨ (¬ p527) ∨ (¬ p528) ∨ (¬ p529) ∨ (¬ p530) ∨ (¬ p531)) : p526 ∨ p515 ∨ p519 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p526) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p515) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p519) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p527 := by
    rcases h2979 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p528 := by
    rcases h2980 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p529 := by
    rcases h2981 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p530 := by
    rcases h2982 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p531 := by
    rcases h2983 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2890 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22220 (p515 p519 p525 p527 p528 p529 p530 p531 : Prop)
    (h2974 : p525 ∨ p527)
    (h2975 : p525 ∨ p528)
    (h2976 : p525 ∨ p529)
    (h2977 : p525 ∨ p530)
    (h2978 : p525 ∨ p531)
    (h2890 : p515 ∨ p519 ∨ (¬ p527) ∨ (¬ p528) ∨ (¬ p529) ∨ (¬ p530) ∨ (¬ p531)) : p525 ∨ p515 ∨ p519 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p525) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p515) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p519) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h2890 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22221 (p515 p519 p524 p527 p528 p529 p530 p531 : Prop)
    (h2969 : p524 ∨ p527)
    (h2970 : p524 ∨ p528)
    (h2971 : p524 ∨ p529)
    (h2972 : p524 ∨ p530)
    (h2973 : p524 ∨ p531)
    (h2890 : p515 ∨ p519 ∨ (¬ p527) ∨ (¬ p528) ∨ (¬ p529) ∨ (¬ p530) ∨ (¬ p531)) : p524 ∨ p515 ∨ p519 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p524) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p515) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p519) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h2890 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22222 (p515 p519 p523 p527 p528 p529 p530 p531 : Prop)
    (h2964 : p523 ∨ p527)
    (h2965 : p523 ∨ p528)
    (h2966 : p523 ∨ p529)
    (h2967 : p523 ∨ p530)
    (h2968 : p523 ∨ p531)
    (h2890 : p515 ∨ p519 ∨ (¬ p527) ∨ (¬ p528) ∨ (¬ p529) ∨ (¬ p530) ∨ (¬ p531)) : p523 ∨ p515 ∨ p519 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p523) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p515) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p519) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h2890 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22225 (p69 p86 p237 p419 p657 p665 p1116 p1187 : Prop)
    (h18688 : (¬ p69) ∨ (¬ p419) ∨ (¬ p657) ∨ (¬ p1187))
    (h18726 : (¬ p69) ∨ (¬ p86) ∨ (¬ p237) ∨ (¬ p419) ∨ (¬ p665) ∨ (¬ p1116) ∨ (¬ p1187))
    (h22069 : p665 ∨ p657) : (¬ p419) ∨ (¬ p237) ∨ (¬ p86) ∨ (¬ p1187) ∨ (¬ p1116) ∨ (¬ p69) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p657) := by
    rcases h18688 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u5)
    · exact False.elim (q1 u0)
    · exact q2
    · exact False.elim (q3 u3)
  have u7 : (¬ p665) := by
    rcases h18726 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u5)
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u0)
    · exact q4
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u3)
  rcases h22069 with q0 | q1
  · exact False.elim (u7 q0)
  · exact False.elim (u6 q1)

theorem step22232 (p325 p331 p332 p337 p338 p339 p340 p341 : Prop)
    (h1799 : p332 ∨ p337)
    (h1800 : p332 ∨ p338)
    (h1801 : p332 ∨ p339)
    (h1802 : p332 ∨ p340)
    (h1803 : p332 ∨ p341)
    (h1733 : p325 ∨ p331 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341)) : p332 ∨ p331 ∨ p325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p332) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p331) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p325) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p337 := by
    rcases h1799 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p338 := by
    rcases h1800 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p339 := by
    rcases h1801 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p340 := by
    rcases h1802 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p341 := by
    rcases h1803 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1733 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22233 (p325 p331 p336 p337 p338 p339 p340 p341 : Prop)
    (h1819 : p336 ∨ p337)
    (h1820 : p336 ∨ p338)
    (h1821 : p336 ∨ p339)
    (h1822 : p336 ∨ p340)
    (h1823 : p336 ∨ p341)
    (h1733 : p325 ∨ p331 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341)) : p336 ∨ p331 ∨ p325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p336) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p331) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p325) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p337 := by
    rcases h1819 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p338 := by
    rcases h1820 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p339 := by
    rcases h1821 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p340 := by
    rcases h1822 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p341 := by
    rcases h1823 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1733 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22234 (p325 p331 p335 p337 p338 p339 p340 p341 : Prop)
    (h1814 : p335 ∨ p337)
    (h1815 : p335 ∨ p338)
    (h1816 : p335 ∨ p339)
    (h1817 : p335 ∨ p340)
    (h1818 : p335 ∨ p341)
    (h1733 : p325 ∨ p331 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341)) : p335 ∨ p331 ∨ p325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p335) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p331) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p325) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p337 := by
    rcases h1814 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p338 := by
    rcases h1815 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p339 := by
    rcases h1816 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p340 := by
    rcases h1817 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p341 := by
    rcases h1818 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1733 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22235 (p325 p331 p334 p337 p338 p339 p340 p341 : Prop)
    (h1809 : p334 ∨ p337)
    (h1810 : p334 ∨ p338)
    (h1811 : p334 ∨ p339)
    (h1812 : p334 ∨ p340)
    (h1813 : p334 ∨ p341)
    (h1733 : p325 ∨ p331 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341)) : p334 ∨ p331 ∨ p325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p334) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p331) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p325) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p337 := by
    rcases h1809 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p338 := by
    rcases h1810 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p339 := by
    rcases h1811 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p340 := by
    rcases h1812 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p341 := by
    rcases h1813 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1733 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22236 (p10 p325 p331 p332 p333 p334 p335 p336 p337 p338 p339 p340 p341 : Prop)
    (h22232 : p332 ∨ p331 ∨ p325)
    (h22233 : p336 ∨ p331 ∨ p325)
    (h22234 : p335 ∨ p331 ∨ p325)
    (h22235 : p334 ∨ p331 ∨ p325)
    (h1713 : p10 ∨ p331 ∨ (¬ p332) ∨ (¬ p333) ∨ (¬ p334) ∨ (¬ p335) ∨ (¬ p336))
    (h1804 : p333 ∨ p337)
    (h1805 : p333 ∨ p338)
    (h1806 : p333 ∨ p339)
    (h1807 : p333 ∨ p340)
    (h1808 : p333 ∨ p341)
    (h1733 : p325 ∨ p331 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341)) : p331 ∨ p325 ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p331) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p332 := by
    rcases h22232 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p336 := by
    rcases h22233 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p335 := by
    rcases h22234 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p334 := by
    rcases h22235 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p333) := by
    rcases h1713 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u3)
    · exact q3
    · exact False.elim (q4 u6)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u4)
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
  have u11 : p340 := by
    rcases h1807 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u12 : p341 := by
    rcases h1808 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h1733 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u12)

theorem step22238 (p104 p108 p111 p112 p113 p114 p115 p116 p117 p118 p119 p120 : Prop)
    (h526 : p104 ∨ p108 ∨ (¬ p111) ∨ (¬ p112) ∨ (¬ p113) ∨ (¬ p114) ∨ (¬ p115))
    (h635 : p114 ∨ p116)
    (h636 : p114 ∨ p117)
    (h637 : p114 ∨ p118)
    (h638 : p114 ∨ p119)
    (h639 : p114 ∨ p120)
    (h551 : p104 ∨ p108 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : (¬ p112) ∨ p108 ∨ p104 ∨ (¬ p115) ∨ (¬ p113) ∨ (¬ p111) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p112 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p108) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p104) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p113 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p111 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p114) := by
    rcases h526 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact q5
    · exact False.elim (q6 u3)
  have u7 : p116 := by
    rcases h635 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p117 := by
    rcases h636 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p118 := by
    rcases h637 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p119 := by
    rcases h638 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p120 := by
    rcases h639 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h551 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22239 (p104 p108 p111 p112 p113 p115 : Prop)
    (h21758 : p115 ∨ p104 ∨ p108)
    (h21761 : p113 ∨ p104 ∨ p108)
    (h21760 : p112 ∨ p104 ∨ p108)
    (h21759 : p111 ∨ p104 ∨ p108)
    (h22238 : (¬ p112) ∨ p108 ∨ p104 ∨ (¬ p115) ∨ (¬ p113) ∨ (¬ p111)) : p108 ∨ p104 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p108) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p104) := fun hu => hn (Or.inr hu)
  have u2 : p115 := by
    rcases h21758 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u3 : p113 := by
    rcases h21761 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u4 : p112 := by
    rcases h21760 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u5 : p111 := by
    rcases h21759 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  rcases h22238 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)

theorem step22240 (p104 p110 p111 p112 p113 p114 p115 p116 p117 p118 p119 p120 : Prop)
    (h529 : p104 ∨ p110 ∨ (¬ p111) ∨ (¬ p112) ∨ (¬ p113) ∨ (¬ p114) ∨ (¬ p115))
    (h620 : p111 ∨ p116)
    (h621 : p111 ∨ p117)
    (h622 : p111 ∨ p118)
    (h623 : p111 ∨ p119)
    (h624 : p111 ∨ p120)
    (h554 : p104 ∨ p110 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : (¬ p114) ∨ (¬ p112) ∨ (¬ p113) ∨ p104 ∨ p110 ∨ (¬ p115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p114 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p112 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p113 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p104) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p110) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p111) := by
    rcases h529 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u4 q1)
    · exact q2
    · exact False.elim (q3 u1)
    · exact False.elim (q4 u2)
    · exact False.elim (q5 u0)
    · exact False.elim (q6 u5)
  have u7 : p116 := by
    rcases h620 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p117 := by
    rcases h621 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p118 := by
    rcases h622 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p119 := by
    rcases h623 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p120 := by
    rcases h624 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h554 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22241 (p104 p110 p112 p113 p114 p115 : Prop)
    (h21817 : p115 ∨ p104 ∨ p110)
    (h21818 : p114 ∨ p104 ∨ p110)
    (h21819 : p113 ∨ p104 ∨ p110)
    (h21820 : p112 ∨ p104 ∨ p110)
    (h22240 : (¬ p114) ∨ (¬ p112) ∨ (¬ p113) ∨ p104 ∨ p110 ∨ (¬ p115)) : p110 ∨ p104 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p110) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p104) := fun hu => hn (Or.inr hu)
  have u2 : p115 := by
    rcases h21817 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u3 : p114 := by
    rcases h21818 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u4 : p113 := by
    rcases h21819 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u5 : p112 := by
    rcases h21820 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  rcases h22240 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (u1 q3)
  · exact False.elim (u0 q4)
  · exact False.elim (q5 u2)

theorem step22242 (p12 p110 p124 p227 p961 p1079 p1083 : Prop)
    (h21044 : p961 ∨ p227)
    (h13431 : (¬ p124) ∨ p227 ∨ (¬ p1083))
    (h18236 : (¬ p12) ∨ (¬ p110) ∨ (¬ p124) ∨ (¬ p961) ∨ (¬ p1079))
    (h20699 : p1079 ∨ p1083) : p227 ∨ (¬ p124) ∨ (¬ p110) ∨ (¬ p12) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p227) := fun hu => hn (Or.inl hu)
  have u1 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p961 := by
    rcases h21044 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : (¬ p1083) := by
    rcases h13431 with q0 | q1 | q2
    · exact False.elim (q0 u1)
    · exact False.elim (u0 q1)
    · exact q2
  have u6 : (¬ p1079) := by
    rcases h18236 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u3)
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u4)
    · exact q4
  rcases h20699 with q0 | q1
  · exact False.elim (u6 q0)
  · exact False.elim (u5 q1)

theorem step22243 (p12 p110 p124 p304 p961 p1079 p1083 : Prop)
    (h21106 : p124 ∨ p304)
    (h14122 : p304 ∨ (¬ p961) ∨ (¬ p1083))
    (h18236 : (¬ p12) ∨ (¬ p110) ∨ (¬ p124) ∨ (¬ p961) ∨ (¬ p1079))
    (h20699 : p1079 ∨ p1083) : (¬ p961) ∨ p304 ∨ (¬ p110) ∨ (¬ p12) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p304) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p124 := by
    rcases h21106 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : (¬ p1083) := by
    rcases h14122 with q0 | q1 | q2
    · exact False.elim (u1 q0)
    · exact False.elim (q1 u0)
    · exact q2
  have u6 : (¬ p1079) := by
    rcases h18236 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u3)
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u0)
    · exact q4
  rcases h20699 with q0 | q1
  · exact False.elim (u6 q0)
  · exact False.elim (u5 q1)

theorem step22244 (p304 p309 p317 p318 p319 p320 p321 p322 : Prop)
    (h1693 : p317 ∨ p318)
    (h1694 : p317 ∨ p319)
    (h1695 : p317 ∨ p320)
    (h1696 : p317 ∨ p321)
    (h1697 : p317 ∨ p322)
    (h1608 : p304 ∨ p309 ∨ (¬ p318) ∨ (¬ p319) ∨ (¬ p320) ∨ (¬ p321) ∨ (¬ p322)) : p317 ∨ p309 ∨ p304 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p317) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p309) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p304) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p318 := by
    rcases h1693 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p319 := by
    rcases h1694 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p320 := by
    rcases h1695 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p321 := by
    rcases h1696 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p322 := by
    rcases h1697 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1608 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22245 (p304 p309 p316 p318 p319 p320 p321 p322 : Prop)
    (h1688 : p316 ∨ p318)
    (h1689 : p316 ∨ p319)
    (h1690 : p316 ∨ p320)
    (h1691 : p316 ∨ p321)
    (h1692 : p316 ∨ p322)
    (h1608 : p304 ∨ p309 ∨ (¬ p318) ∨ (¬ p319) ∨ (¬ p320) ∨ (¬ p321) ∨ (¬ p322)) : p316 ∨ p309 ∨ p304 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p316) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p309) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p304) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p318 := by
    rcases h1688 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p319 := by
    rcases h1689 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p320 := by
    rcases h1690 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p321 := by
    rcases h1691 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p322 := by
    rcases h1692 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1608 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22246 (p304 p309 p315 p318 p319 p320 p321 p322 : Prop)
    (h1683 : p315 ∨ p318)
    (h1684 : p315 ∨ p319)
    (h1685 : p315 ∨ p320)
    (h1686 : p315 ∨ p321)
    (h1687 : p315 ∨ p322)
    (h1608 : p304 ∨ p309 ∨ (¬ p318) ∨ (¬ p319) ∨ (¬ p320) ∨ (¬ p321) ∨ (¬ p322)) : p315 ∨ p309 ∨ p304 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p315) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p309) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p304) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p318 := by
    rcases h1683 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p319 := by
    rcases h1684 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p320 := by
    rcases h1685 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p321 := by
    rcases h1686 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p322 := by
    rcases h1687 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1608 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22247 (p304 p309 p314 p318 p319 p320 p321 p322 : Prop)
    (h1678 : p314 ∨ p318)
    (h1679 : p314 ∨ p319)
    (h1680 : p314 ∨ p320)
    (h1681 : p314 ∨ p321)
    (h1682 : p314 ∨ p322)
    (h1608 : p304 ∨ p309 ∨ (¬ p318) ∨ (¬ p319) ∨ (¬ p320) ∨ (¬ p321) ∨ (¬ p322)) : p314 ∨ p309 ∨ p304 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p314) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p309) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p304) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p318 := by
    rcases h1678 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p319 := by
    rcases h1679 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p320 := by
    rcases h1680 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p321 := by
    rcases h1681 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p322 := by
    rcases h1682 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1608 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22248 (p304 p309 p313 p314 p315 p316 p317 p318 p319 p320 p321 p322 : Prop)
    (h1583 : p304 ∨ p309 ∨ (¬ p313) ∨ (¬ p314) ∨ (¬ p315) ∨ (¬ p316) ∨ (¬ p317))
    (h1673 : p313 ∨ p318)
    (h1674 : p313 ∨ p319)
    (h1675 : p313 ∨ p320)
    (h1676 : p313 ∨ p321)
    (h1677 : p313 ∨ p322)
    (h1608 : p304 ∨ p309 ∨ (¬ p318) ∨ (¬ p319) ∨ (¬ p320) ∨ (¬ p321) ∨ (¬ p322)) : (¬ p314) ∨ (¬ p317) ∨ p304 ∨ p309 ∨ (¬ p315) ∨ (¬ p316) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p314 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p317 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p304) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p309) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p315 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p316 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p313) := by
    rcases h1583 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p318 := by
    rcases h1673 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p319 := by
    rcases h1674 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p320 := by
    rcases h1675 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p321 := by
    rcases h1676 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p322 := by
    rcases h1677 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h1608 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22249 (p304 p309 p314 p315 p316 p317 : Prop)
    (h22244 : p317 ∨ p309 ∨ p304)
    (h22245 : p316 ∨ p309 ∨ p304)
    (h22246 : p315 ∨ p309 ∨ p304)
    (h22247 : p314 ∨ p309 ∨ p304)
    (h22248 : (¬ p314) ∨ (¬ p317) ∨ p304 ∨ p309 ∨ (¬ p315) ∨ (¬ p316)) : p309 ∨ p304 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p309) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p304) := fun hu => hn (Or.inr hu)
  have u2 : p317 := by
    rcases h22244 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p316 := by
    rcases h22245 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p315 := by
    rcases h22246 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p314 := by
    rcases h22247 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22248 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22250 (p262 p268 p269 p270 p271 p272 p273 p274 p275 p276 p277 p278 : Prop)
    (h1347 : p262 ∨ p268 ∨ (¬ p274) ∨ (¬ p275) ∨ (¬ p276) ∨ (¬ p277) ∨ (¬ p278))
    (h1414 : p269 ∨ p275)
    (h1419 : p270 ∨ p275)
    (h1424 : p271 ∨ p275)
    (h1429 : p272 ∨ p275)
    (h1434 : p273 ∨ p275)
    (h1322 : p262 ∨ p268 ∨ (¬ p269) ∨ (¬ p270) ∨ (¬ p271) ∨ (¬ p272) ∨ (¬ p273)) : (¬ p278) ∨ (¬ p276) ∨ p262 ∨ (¬ p274) ∨ p268 ∨ (¬ p277) := by
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
  have u2 : (¬ p262) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p274 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p268) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p277 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p275) := by
    rcases h1347 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u4 q1)
    · exact False.elim (q2 u3)
    · exact q3
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u5)
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
  rcases h1322 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22251 (p17 p262 p268 p274 p276 p277 p278 : Prop)
    (h21695 : p276 ∨ p268 ∨ p17)
    (h21696 : p277 ∨ p268 ∨ p17)
    (h21697 : p278 ∨ p268 ∨ p17)
    (h21698 : p274 ∨ p268 ∨ p17)
    (h22250 : (¬ p278) ∨ (¬ p276) ∨ p262 ∨ (¬ p274) ∨ p268 ∨ (¬ p277)) : p268 ∨ p262 ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p268) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p262) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p276 := by
    rcases h21695 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u4 : p277 := by
    rcases h21696 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u5 : p278 := by
    rcases h21697 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u6 : p274 := by
    rcases h21698 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  rcases h22250 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (u0 q4)
  · exact False.elim (q5 u4)

theorem step22252 (p12 p104 p108 p139 p258 p268 p309 p310 p1055 p1061 p1076 : Prop)
    (h7021 : (¬ p12) ∨ (¬ p104) ∨ (¬ p1076))
    (h22239 : p108 ∨ p104)
    (h18076 : (¬ p12) ∨ (¬ p108) ∨ (¬ p139) ∨ (¬ p258) ∨ (¬ p309) ∨ (¬ p1055))
    (h16407 : (¬ p258) ∨ (¬ p268) ∨ (¬ p310) ∨ (¬ p1061) ∨ (¬ p1076))
    (h20663 : p1061 ∨ p1055) : (¬ p258) ∨ (¬ p268) ∨ (¬ p309) ∨ (¬ p310) ∨ (¬ p139) ∨ (¬ p1076) ∨ (¬ p12) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p268 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p139 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p104) := by
    rcases h7021 with q0 | q1 | q2
    · exact False.elim (q0 u6)
    · exact q1
    · exact False.elim (q2 u5)
  have u8 : p108 := by
    rcases h22239 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : (¬ p1055) := by
    rcases h18076 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u6)
    · exact False.elim (q1 u8)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u2)
    · exact q5
  have u10 : (¬ p1061) := by
    rcases h16407 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u0)
    · exact False.elim (q1 u1)
    · exact False.elim (q2 u3)
    · exact q3
    · exact False.elim (q4 u5)
  rcases h20663 with q0 | q1
  · exact False.elim (u10 q0)
  · exact False.elim (u9 q1)

theorem step22253 (p11 p12 p110 p288 p1079 p1083 p1443 : Prop)
    (h9412 : (¬ p11) ∨ (¬ p1443))
    (h12290 : (¬ p288) ∨ (¬ p1083) ∨ p1443)
    (h18230 : (¬ p11) ∨ (¬ p12) ∨ (¬ p110) ∨ (¬ p288) ∨ (¬ p1079))
    (h20699 : p1079 ∨ p1083) : (¬ p288) ∨ (¬ p110) ∨ (¬ p12) ∨ (¬ p11) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p1443) := by
    rcases h9412 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  have u5 : (¬ p1083) := by
    rcases h12290 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (u4 q2)
  have u6 : (¬ p1079) := by
    rcases h18230 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u3)
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u0)
    · exact q4
  rcases h20699 with q0 | q1
  · exact False.elim (u6 q0)
  · exact False.elim (u5 q1)

theorem step22255 (p15 p22 p125 p362 p425 p494 p499 p601 : Prop)
    (h21038 : p125 ∨ p362)
    (h13656 : p362 ∨ (¬ p425) ∨ (¬ p601))
    (h18508 : (¬ p15) ∨ (¬ p22) ∨ (¬ p125) ∨ (¬ p494) ∨ (¬ p601))
    (h21049 : p494 ∨ p425 ∨ p499) : p362 ∨ p499 ∨ (¬ p15) ∨ (¬ p601) ∨ (¬ p22) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p362) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p499) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p22 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p125 := by
    rcases h21038 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : (¬ p425) := by
    rcases h13656 with q0 | q1 | q2
    · exact False.elim (u0 q0)
    · exact q1
    · exact False.elim (q2 u3)
  have u7 : (¬ p494) := by
    rcases h18508 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u2)
    · exact False.elim (q1 u4)
    · exact False.elim (q2 u5)
    · exact q3
    · exact False.elim (q4 u3)
  rcases h21049 with q0 | q1 | q2
  · exact False.elim (u7 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (u1 q2)

theorem step22256 (p124 p305 p345 p350 p362 p1055 p1077 : Prop)
    (h21498 : p305 ∨ p124)
    (h14342 : p124 ∨ (¬ p345) ∨ (¬ p362))
    (h17958 : (¬ p305) ∨ (¬ p350) ∨ (¬ p362) ∨ (¬ p1055) ∨ (¬ p1077))
    (h21667 : p350 ∨ p345) : (¬ p362) ∨ (¬ p1055) ∨ p124 ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p305 := by
    rcases h21498 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : (¬ p345) := by
    rcases h14342 with q0 | q1 | q2
    · exact False.elim (u2 q0)
    · exact q1
    · exact False.elim (q2 u0)
  have u6 : (¬ p350) := by
    rcases h17958 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u4)
    · exact q1
    · exact False.elim (q2 u0)
    · exact False.elim (q3 u1)
    · exact False.elim (q4 u3)
  rcases h21667 with q0 | q1
  · exact False.elim (u6 q0)
  · exact False.elim (u5 q1)

theorem step22258 (p2 p5 p41 p63 p156 p163 p170 p193 p238 p241 p419 p665 p928 p1055 p1116 : Prop)
    (h8743 : (¬ p241) ∨ (¬ p1055) ∨ (¬ p1116))
    (h17977 : (¬ p2) ∨ (¬ p5) ∨ (¬ p63) ∨ (¬ p419) ∨ (¬ p665) ∨ (¬ p928) ∨ (¬ p1116))
    (h22007 : p238 ∨ p241)
    (h13917 : (¬ p41) ∨ (¬ p170) ∨ p928)
    (h16610 : (¬ p156) ∨ (¬ p193) ∨ (¬ p238) ∨ (¬ p1055) ∨ (¬ p1116))
    (h22001 : p156 ∨ p170 ∨ p163) : (¬ p1116) ∨ (¬ p63) ∨ (¬ p665) ∨ (¬ p1055) ∨ (¬ p419) ∨ (¬ p41) ∨ p163 ∨ (¬ p193) ∨ (¬ p5) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p241) := by
    rcases h8743 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (q2 u0)
  have u11 : (¬ p928) := by
    rcases h17977 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u9)
    · exact False.elim (q1 u8)
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u2)
    · exact q5
    · exact False.elim (q6 u0)
  have u12 : p238 := by
    rcases h22007 with q0 | q1
    · exact q0
    · exact False.elim (u10 q1)
  have u13 : (¬ p170) := by
    rcases h13917 with q0 | q1 | q2
    · exact False.elim (q0 u5)
    · exact q1
    · exact False.elim (u11 q2)
  have u14 : (¬ p156) := by
    rcases h16610 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u7)
    · exact False.elim (q2 u12)
    · exact False.elim (q3 u3)
    · exact False.elim (q4 u0)
  rcases h22001 with q0 | q1 | q2
  · exact False.elim (u14 q0)
  · exact False.elim (u13 q1)
  · exact False.elim (u6 q2)

theorem step22260 (p238 p242 p247 p250 p251 p252 p253 p254 : Prop)
    (h1290 : p247 ∨ p250)
    (h1291 : p247 ∨ p251)
    (h1292 : p247 ∨ p252)
    (h1293 : p247 ∨ p253)
    (h1294 : p247 ∨ p254)
    (h1206 : p238 ∨ p242 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : p247 ∨ p242 ∨ p238 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p247) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p242) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p238) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p250 := by
    rcases h1290 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p251 := by
    rcases h1291 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p252 := by
    rcases h1292 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p253 := by
    rcases h1293 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p254 := by
    rcases h1294 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1206 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22261 (p238 p242 p246 p250 p251 p252 p253 p254 : Prop)
    (h1285 : p246 ∨ p250)
    (h1286 : p246 ∨ p251)
    (h1287 : p246 ∨ p252)
    (h1288 : p246 ∨ p253)
    (h1289 : p246 ∨ p254)
    (h1206 : p238 ∨ p242 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : p246 ∨ p242 ∨ p238 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p246) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p242) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p238) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p250 := by
    rcases h1285 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p251 := by
    rcases h1286 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p252 := by
    rcases h1287 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p253 := by
    rcases h1288 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p254 := by
    rcases h1289 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1206 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22262 (p238 p242 p245 p250 p251 p252 p253 p254 : Prop)
    (h1280 : p245 ∨ p250)
    (h1281 : p245 ∨ p251)
    (h1282 : p245 ∨ p252)
    (h1283 : p245 ∨ p253)
    (h1284 : p245 ∨ p254)
    (h1206 : p238 ∨ p242 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : p245 ∨ p242 ∨ p238 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p245) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p242) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p238) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p250 := by
    rcases h1280 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p251 := by
    rcases h1281 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p252 := by
    rcases h1282 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p253 := by
    rcases h1283 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p254 := by
    rcases h1284 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1206 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22263 (p238 p242 p249 p250 p251 p252 p253 p254 : Prop)
    (h1300 : p249 ∨ p250)
    (h1301 : p249 ∨ p251)
    (h1302 : p249 ∨ p252)
    (h1303 : p249 ∨ p253)
    (h1304 : p249 ∨ p254)
    (h1206 : p238 ∨ p242 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : p249 ∨ p242 ∨ p238 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p249) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p242) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p238) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p250 := by
    rcases h1300 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p251 := by
    rcases h1301 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p252 := by
    rcases h1302 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p253 := by
    rcases h1303 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p254 := by
    rcases h1304 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1206 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22264 (p238 p242 p245 p246 p247 p248 p249 p250 p251 p252 p253 p254 : Prop)
    (h1181 : p238 ∨ p242 ∨ (¬ p245) ∨ (¬ p246) ∨ (¬ p247) ∨ (¬ p248) ∨ (¬ p249))
    (h1295 : p248 ∨ p250)
    (h1296 : p248 ∨ p251)
    (h1297 : p248 ∨ p252)
    (h1298 : p248 ∨ p253)
    (h1299 : p248 ∨ p254)
    (h1206 : p238 ∨ p242 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : (¬ p249) ∨ (¬ p246) ∨ p238 ∨ p242 ∨ (¬ p247) ∨ (¬ p245) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p246 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p238) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p242) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p247 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p245 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p248) := by
    rcases h1181 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u1)
    · exact False.elim (q4 u4)
    · exact q5
    · exact False.elim (q6 u0)
  have u7 : p250 := by
    rcases h1295 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p251 := by
    rcases h1296 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p252 := by
    rcases h1297 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p253 := by
    rcases h1298 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p254 := by
    rcases h1299 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h1206 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22265 (p238 p242 p245 p246 p247 p249 : Prop)
    (h22260 : p247 ∨ p242 ∨ p238)
    (h22261 : p246 ∨ p242 ∨ p238)
    (h22262 : p245 ∨ p242 ∨ p238)
    (h22263 : p249 ∨ p242 ∨ p238)
    (h22264 : (¬ p249) ∨ (¬ p246) ∨ p238 ∨ p242 ∨ (¬ p247) ∨ (¬ p245)) : p242 ∨ p238 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p242) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p238) := fun hu => hn (Or.inr hu)
  have u2 : p247 := by
    rcases h22260 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p246 := by
    rcases h22261 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p245 := by
    rcases h22262 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p249 := by
    rcases h22263 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22264 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u4)

theorem step22266 (p43 p49 p53 p56 p57 p58 p59 p60 : Prop)
    (h243 : p53 ∨ p56)
    (h244 : p53 ∨ p57)
    (h245 : p53 ∨ p58)
    (h246 : p53 ∨ p59)
    (h247 : p53 ∨ p60)
    (h161 : p43 ∨ p49 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60)) : p53 ∨ p49 ∨ p43 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p53) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p49) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p43) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p56 := by
    rcases h243 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p57 := by
    rcases h244 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p58 := by
    rcases h245 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p59 := by
    rcases h246 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p60 := by
    rcases h247 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h161 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22267 (p43 p49 p52 p56 p57 p58 p59 p60 : Prop)
    (h238 : p52 ∨ p56)
    (h239 : p52 ∨ p57)
    (h240 : p52 ∨ p58)
    (h241 : p52 ∨ p59)
    (h242 : p52 ∨ p60)
    (h161 : p43 ∨ p49 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60)) : p52 ∨ p49 ∨ p43 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p52) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p49) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p43) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p56 := by
    rcases h238 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p57 := by
    rcases h239 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p58 := by
    rcases h240 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p59 := by
    rcases h241 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p60 := by
    rcases h242 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h161 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22268 (p43 p49 p51 p56 p57 p58 p59 p60 : Prop)
    (h233 : p51 ∨ p56)
    (h234 : p51 ∨ p57)
    (h235 : p51 ∨ p58)
    (h236 : p51 ∨ p59)
    (h237 : p51 ∨ p60)
    (h161 : p43 ∨ p49 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60)) : p51 ∨ p49 ∨ p43 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p51) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p49) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p43) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p56 := by
    rcases h233 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p57 := by
    rcases h234 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p58 := by
    rcases h235 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p59 := by
    rcases h236 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p60 := by
    rcases h237 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h161 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22269 (p43 p49 p55 p56 p57 p58 p59 p60 : Prop)
    (h253 : p55 ∨ p56)
    (h254 : p55 ∨ p57)
    (h255 : p55 ∨ p58)
    (h256 : p55 ∨ p59)
    (h257 : p55 ∨ p60)
    (h161 : p43 ∨ p49 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60)) : p55 ∨ p49 ∨ p43 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p55) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p49) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p43) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p56 := by
    rcases h253 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p57 := by
    rcases h254 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p58 := by
    rcases h255 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p59 := by
    rcases h256 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p60 := by
    rcases h257 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h161 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22270 (p43 p49 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 : Prop)
    (h136 : p43 ∨ p49 ∨ (¬ p51) ∨ (¬ p52) ∨ (¬ p53) ∨ (¬ p54) ∨ (¬ p55))
    (h248 : p54 ∨ p56)
    (h249 : p54 ∨ p57)
    (h250 : p54 ∨ p58)
    (h251 : p54 ∨ p59)
    (h252 : p54 ∨ p60)
    (h161 : p43 ∨ p49 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60)) : (¬ p55) ∨ (¬ p52) ∨ p43 ∨ (¬ p53) ∨ p49 ∨ (¬ p51) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p55 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p52 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p43) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p53 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p49) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p51 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p54) := by
    rcases h136 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u4 q1)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u1)
    · exact False.elim (q4 u3)
    · exact q5
    · exact False.elim (q6 u0)
  have u7 : p56 := by
    rcases h248 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p57 := by
    rcases h249 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p58 := by
    rcases h250 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p59 := by
    rcases h251 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p60 := by
    rcases h252 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h161 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22271 (p43 p49 p51 p52 p53 p55 : Prop)
    (h22266 : p53 ∨ p49 ∨ p43)
    (h22267 : p52 ∨ p49 ∨ p43)
    (h22268 : p51 ∨ p49 ∨ p43)
    (h22269 : p55 ∨ p49 ∨ p43)
    (h22270 : (¬ p55) ∨ (¬ p52) ∨ p43 ∨ (¬ p53) ∨ p49 ∨ (¬ p51)) : p49 ∨ p43 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p49) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p43) := fun hu => hn (Or.inr hu)
  have u2 : p53 := by
    rcases h22266 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p52 := by
    rcases h22267 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p51 := by
    rcases h22268 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p55 := by
    rcases h22269 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22270 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (u0 q4)
  · exact False.elim (q5 u4)

theorem step22272 (p84 p89 p91 p96 p97 p98 p99 p100 : Prop)
    (h494 : p91 ∨ p96)
    (h495 : p91 ∨ p97)
    (h496 : p91 ∨ p98)
    (h497 : p91 ∨ p99)
    (h498 : p91 ∨ p100)
    (h425 : p84 ∨ p89 ∨ (¬ p96) ∨ (¬ p97) ∨ (¬ p98) ∨ (¬ p99) ∨ (¬ p100)) : p91 ∨ p89 ∨ p84 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p91) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p89) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p84) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p96 := by
    rcases h494 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p97 := by
    rcases h495 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p98 := by
    rcases h496 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p99 := by
    rcases h497 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p100 := by
    rcases h498 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h425 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22273 (p84 p89 p95 p96 p97 p98 p99 p100 : Prop)
    (h514 : p95 ∨ p96)
    (h515 : p95 ∨ p97)
    (h516 : p95 ∨ p98)
    (h517 : p95 ∨ p99)
    (h518 : p95 ∨ p100)
    (h425 : p84 ∨ p89 ∨ (¬ p96) ∨ (¬ p97) ∨ (¬ p98) ∨ (¬ p99) ∨ (¬ p100)) : p95 ∨ p89 ∨ p84 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p95) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p89) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p84) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p96 := by
    rcases h514 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p97 := by
    rcases h515 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p98 := by
    rcases h516 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p99 := by
    rcases h517 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p100 := by
    rcases h518 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h425 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22274 (p84 p89 p94 p96 p97 p98 p99 p100 : Prop)
    (h509 : p94 ∨ p96)
    (h510 : p94 ∨ p97)
    (h511 : p94 ∨ p98)
    (h512 : p94 ∨ p99)
    (h513 : p94 ∨ p100)
    (h425 : p84 ∨ p89 ∨ (¬ p96) ∨ (¬ p97) ∨ (¬ p98) ∨ (¬ p99) ∨ (¬ p100)) : p94 ∨ p89 ∨ p84 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p94) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p89) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p84) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p96 := by
    rcases h509 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p97 := by
    rcases h510 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p98 := by
    rcases h511 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p99 := by
    rcases h512 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p100 := by
    rcases h513 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h425 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22275 (p84 p89 p93 p96 p97 p98 p99 p100 : Prop)
    (h504 : p93 ∨ p96)
    (h505 : p93 ∨ p97)
    (h506 : p93 ∨ p98)
    (h507 : p93 ∨ p99)
    (h508 : p93 ∨ p100)
    (h425 : p84 ∨ p89 ∨ (¬ p96) ∨ (¬ p97) ∨ (¬ p98) ∨ (¬ p99) ∨ (¬ p100)) : p93 ∨ p89 ∨ p84 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p93) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p89) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p84) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p96 := by
    rcases h504 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p97 := by
    rcases h505 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p98 := by
    rcases h506 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p99 := by
    rcases h507 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p100 := by
    rcases h508 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h425 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22276 (p84 p89 p91 p92 p93 p94 p95 p96 p97 p98 p99 p100 : Prop)
    (h400 : p84 ∨ p89 ∨ (¬ p91) ∨ (¬ p92) ∨ (¬ p93) ∨ (¬ p94) ∨ (¬ p95))
    (h499 : p92 ∨ p96)
    (h500 : p92 ∨ p97)
    (h501 : p92 ∨ p98)
    (h502 : p92 ∨ p99)
    (h503 : p92 ∨ p100)
    (h425 : p84 ∨ p89 ∨ (¬ p96) ∨ (¬ p97) ∨ (¬ p98) ∨ (¬ p99) ∨ (¬ p100)) : (¬ p93) ∨ (¬ p94) ∨ (¬ p95) ∨ p89 ∨ p84 ∨ (¬ p91) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p93 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p94 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p95 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p89) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p84) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p91 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p92) := by
    rcases h400 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u4 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u5)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u1)
    · exact False.elim (q6 u2)
  have u7 : p96 := by
    rcases h499 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p97 := by
    rcases h500 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p98 := by
    rcases h501 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p99 := by
    rcases h502 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p100 := by
    rcases h503 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h425 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22277 (p84 p89 p91 p93 p94 p95 : Prop)
    (h22272 : p91 ∨ p89 ∨ p84)
    (h22273 : p95 ∨ p89 ∨ p84)
    (h22274 : p94 ∨ p89 ∨ p84)
    (h22275 : p93 ∨ p89 ∨ p84)
    (h22276 : (¬ p93) ∨ (¬ p94) ∨ (¬ p95) ∨ p89 ∨ p84 ∨ (¬ p91)) : p89 ∨ p84 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p89) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p84) := fun hu => hn (Or.inr hu)
  have u2 : p91 := by
    rcases h22272 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p95 := by
    rcases h22273 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p94 := by
    rcases h22274 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p93 := by
    rcases h22275 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22276 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (u0 q3)
  · exact False.elim (u1 q4)
  · exact False.elim (q5 u2)

theorem step22278 (p84 p85 p88 p89 : Prop)
    (h9405 : p84 ∨ p88)
    (h14053 : (¬ p85) ∨ (¬ p88) ∨ (¬ p89))
    (h22277 : p89 ∨ p84) : p84 ∨ (¬ p85) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p84) := fun hu => hn (Or.inl hu)
  have u1 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p88 := by
    rcases h9405 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u3 : (¬ p89) := by
    rcases h14053 with q0 | q1 | q2
    · exact False.elim (q0 u1)
    · exact False.elim (q1 u2)
    · exact q2
  rcases h22277 with q0 | q1
  · exact False.elim (u3 q0)
  · exact False.elim (u0 q1)

theorem step22279 (p185 p242 p248 p250 p251 p252 p253 p254 : Prop)
    (h1295 : p248 ∨ p250)
    (h1296 : p248 ∨ p251)
    (h1297 : p248 ∨ p252)
    (h1298 : p248 ∨ p253)
    (h1299 : p248 ∨ p254)
    (h1216 : p185 ∨ p242 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : p248 ∨ p242 ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p248) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p242) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p250 := by
    rcases h1295 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p251 := by
    rcases h1296 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p252 := by
    rcases h1297 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p253 := by
    rcases h1298 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p254 := by
    rcases h1299 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1216 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22280 (p185 p242 p247 p250 p251 p252 p253 p254 : Prop)
    (h1290 : p247 ∨ p250)
    (h1291 : p247 ∨ p251)
    (h1292 : p247 ∨ p252)
    (h1293 : p247 ∨ p253)
    (h1294 : p247 ∨ p254)
    (h1216 : p185 ∨ p242 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : p247 ∨ p242 ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p247) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p242) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p250 := by
    rcases h1290 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p251 := by
    rcases h1291 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p252 := by
    rcases h1292 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p253 := by
    rcases h1293 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p254 := by
    rcases h1294 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1216 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22281 (p185 p242 p246 p250 p251 p252 p253 p254 : Prop)
    (h1285 : p246 ∨ p250)
    (h1286 : p246 ∨ p251)
    (h1287 : p246 ∨ p252)
    (h1288 : p246 ∨ p253)
    (h1289 : p246 ∨ p254)
    (h1216 : p185 ∨ p242 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : p246 ∨ p242 ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p246) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p242) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p250 := by
    rcases h1285 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p251 := by
    rcases h1286 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p252 := by
    rcases h1287 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p253 := by
    rcases h1288 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p254 := by
    rcases h1289 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1216 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22282 (p185 p242 p245 p250 p251 p252 p253 p254 : Prop)
    (h1280 : p245 ∨ p250)
    (h1281 : p245 ∨ p251)
    (h1282 : p245 ∨ p252)
    (h1283 : p245 ∨ p253)
    (h1284 : p245 ∨ p254)
    (h1216 : p185 ∨ p242 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : p245 ∨ p242 ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p245) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p242) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p250 := by
    rcases h1280 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p251 := by
    rcases h1281 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p252 := by
    rcases h1282 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p253 := by
    rcases h1283 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p254 := by
    rcases h1284 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1216 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22283 (p185 p242 p245 p246 p247 p248 p249 p250 p251 p252 p253 p254 : Prop)
    (h1191 : p185 ∨ p242 ∨ (¬ p245) ∨ (¬ p246) ∨ (¬ p247) ∨ (¬ p248) ∨ (¬ p249))
    (h1300 : p249 ∨ p250)
    (h1301 : p249 ∨ p251)
    (h1302 : p249 ∨ p252)
    (h1303 : p249 ∨ p253)
    (h1304 : p249 ∨ p254)
    (h1216 : p185 ∨ p242 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : (¬ p245) ∨ (¬ p248) ∨ p185 ∨ (¬ p247) ∨ p242 ∨ (¬ p246) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p245 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p248 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p247 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p242) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p246 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p249) := by
    rcases h1191 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u4 q1)
    · exact False.elim (q2 u0)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u1)
    · exact q6
  have u7 : p250 := by
    rcases h1300 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p251 := by
    rcases h1301 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p252 := by
    rcases h1302 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p253 := by
    rcases h1303 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p254 := by
    rcases h1304 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h1216 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22284 (p185 p242 p245 p246 p247 p248 : Prop)
    (h22279 : p248 ∨ p242 ∨ p185)
    (h22280 : p247 ∨ p242 ∨ p185)
    (h22281 : p246 ∨ p242 ∨ p185)
    (h22282 : p245 ∨ p242 ∨ p185)
    (h22283 : (¬ p245) ∨ (¬ p248) ∨ p185 ∨ (¬ p247) ∨ p242 ∨ (¬ p246)) : p242 ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p242) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr hu)
  have u2 : p248 := by
    rcases h22279 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p247 := by
    rcases h22280 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p246 := by
    rcases h22281 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p245 := by
    rcases h22282 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22283 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (u0 q4)
  · exact False.elim (q5 u4)

theorem step22286 (p594 p596 p608 p609 p610 p611 p612 p613 : Prop)
    (h3485 : p608 ∨ p609)
    (h3486 : p608 ∨ p610)
    (h3487 : p608 ∨ p611)
    (h3488 : p608 ∨ p612)
    (h3489 : p608 ∨ p613)
    (h3390 : p594 ∨ p596 ∨ (¬ p609) ∨ (¬ p610) ∨ (¬ p611) ∨ (¬ p612) ∨ (¬ p613)) : p608 ∨ p596 ∨ p594 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p608) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p596) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p594) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p609 := by
    rcases h3485 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p610 := by
    rcases h3486 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p611 := by
    rcases h3487 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p612 := by
    rcases h3488 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p613 := by
    rcases h3489 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3390 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22287 (p594 p596 p607 p609 p610 p611 p612 p613 : Prop)
    (h3480 : p607 ∨ p609)
    (h3481 : p607 ∨ p610)
    (h3482 : p607 ∨ p611)
    (h3483 : p607 ∨ p612)
    (h3484 : p607 ∨ p613)
    (h3390 : p594 ∨ p596 ∨ (¬ p609) ∨ (¬ p610) ∨ (¬ p611) ∨ (¬ p612) ∨ (¬ p613)) : p607 ∨ p596 ∨ p594 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p607) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p596) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p594) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h3390 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22288 (p594 p596 p606 p609 p610 p611 p612 p613 : Prop)
    (h3475 : p606 ∨ p609)
    (h3476 : p606 ∨ p610)
    (h3477 : p606 ∨ p611)
    (h3478 : p606 ∨ p612)
    (h3479 : p606 ∨ p613)
    (h3390 : p594 ∨ p596 ∨ (¬ p609) ∨ (¬ p610) ∨ (¬ p611) ∨ (¬ p612) ∨ (¬ p613)) : p606 ∨ p596 ∨ p594 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p606) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p596) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p594) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h3390 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22289 (p594 p596 p605 p609 p610 p611 p612 p613 : Prop)
    (h3470 : p605 ∨ p609)
    (h3471 : p605 ∨ p610)
    (h3472 : p605 ∨ p611)
    (h3473 : p605 ∨ p612)
    (h3474 : p605 ∨ p613)
    (h3390 : p594 ∨ p596 ∨ (¬ p609) ∨ (¬ p610) ∨ (¬ p611) ∨ (¬ p612) ∨ (¬ p613)) : p605 ∨ p596 ∨ p594 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p605) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p596) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p594) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h3390 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22290 (p594 p596 p604 p605 p606 p607 p608 p609 p610 p611 p612 p613 : Prop)
    (h3365 : p594 ∨ p596 ∨ (¬ p604) ∨ (¬ p605) ∨ (¬ p606) ∨ (¬ p607) ∨ (¬ p608))
    (h3465 : p604 ∨ p609)
    (h3466 : p604 ∨ p610)
    (h3467 : p604 ∨ p611)
    (h3468 : p604 ∨ p612)
    (h3469 : p604 ∨ p613)
    (h3390 : p594 ∨ p596 ∨ (¬ p609) ∨ (¬ p610) ∨ (¬ p611) ∨ (¬ p612) ∨ (¬ p613)) : (¬ p605) ∨ (¬ p608) ∨ p594 ∨ p596 ∨ (¬ p606) ∨ (¬ p607) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p605 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p608 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p594) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p596) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p606 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p607 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p604) := by
    rcases h3365 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p609 := by
    rcases h3465 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p610 := by
    rcases h3466 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p611 := by
    rcases h3467 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p612 := by
    rcases h3468 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p613 := by
    rcases h3469 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h3390 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22291 (p594 p596 p605 p606 p607 p608 : Prop)
    (h22286 : p608 ∨ p596 ∨ p594)
    (h22287 : p607 ∨ p596 ∨ p594)
    (h22288 : p606 ∨ p596 ∨ p594)
    (h22289 : p605 ∨ p596 ∨ p594)
    (h22290 : (¬ p605) ∨ (¬ p608) ∨ p594 ∨ p596 ∨ (¬ p606) ∨ (¬ p607)) : p596 ∨ p594 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p596) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p594) := fun hu => hn (Or.inr hu)
  have u2 : p608 := by
    rcases h22286 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p607 := by
    rcases h22287 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p606 := by
    rcases h22288 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p605 := by
    rcases h22289 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22290 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22292 (p21 p101 p350 p495 p594 p595 p596 p616 : Prop)
    (h21790 : p616 ∨ p595)
    (h12881 : (¬ p495) ∨ (¬ p594) ∨ p616)
    (h18462 : (¬ p21) ∨ (¬ p101) ∨ (¬ p350) ∨ (¬ p495) ∨ (¬ p595) ∨ (¬ p596))
    (h22291 : p596 ∨ p594) : p616 ∨ (¬ p101) ∨ (¬ p350) ∨ (¬ p495) ∨ (¬ p21) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p616) := fun hu => hn (Or.inl hu)
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
  have u4 : p21 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p595 := by
    rcases h21790 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : (¬ p594) := by
    rcases h12881 with q0 | q1 | q2
    · exact False.elim (q0 u3)
    · exact q1
    · exact False.elim (u0 q2)
  have u7 : (¬ p596) := by
    rcases h18462 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u4)
    · exact False.elim (q1 u1)
    · exact False.elim (q2 u2)
    · exact False.elim (q3 u3)
    · exact False.elim (q4 u5)
    · exact q5
  rcases h22291 with q0 | q1
  · exact False.elim (u7 q0)
  · exact False.elim (u6 q1)

theorem step22297 (p12 p159 p168 p928 p1116 p1118 p1122 p1249 p1269 p1273 : Prop)
    (h20866 : p1273 ∨ p1269)
    (h21525 : p1273 ∨ p1249)
    (h22117 : p159 ∨ p1273)
    (h18287 : (¬ p12) ∨ (¬ p168) ∨ (¬ p928) ∨ (¬ p1118) ∨ (¬ p1249))
    (h11928 : (¬ p159) ∨ (¬ p928) ∨ (¬ p1122) ∨ (¬ p1269))
    (h21918 : p1118 ∨ p1122 ∨ p1116) : p1273 ∨ (¬ p928) ∨ (¬ p168) ∨ p1116 ∨ (¬ p12) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1273) := fun hu => hn (Or.inl hu)
  have u1 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p168 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1116) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1269 := by
    rcases h20866 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1249 := by
    rcases h21525 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p159 := by
    rcases h22117 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : (¬ p1118) := by
    rcases h18287 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u4)
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u1)
    · exact q3
    · exact False.elim (q4 u6)
  have u9 : (¬ p1122) := by
    rcases h11928 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u7)
    · exact False.elim (q1 u1)
    · exact q2
    · exact False.elim (q3 u5)
  rcases h21918 with q0 | q1 | q2
  · exact False.elim (u8 q0)
  · exact False.elim (u9 q1)
  · exact False.elim (u3 q2)

theorem step22298 (p1055 p1060 p1064 p1065 p1066 p1067 p1068 p1069 p1070 p1071 p1072 p1073 : Prop)
    (h6258 : p1055 ∨ p1060 ∨ (¬ p1069) ∨ (¬ p1070) ∨ (¬ p1071) ∨ (¬ p1072) ∨ (¬ p1073))
    (h6326 : p1064 ∨ p1072)
    (h6331 : p1065 ∨ p1072)
    (h6336 : p1066 ∨ p1072)
    (h6341 : p1067 ∨ p1072)
    (h6346 : p1068 ∨ p1072)
    (h6233 : p1055 ∨ p1060 ∨ (¬ p1064) ∨ (¬ p1065) ∨ (¬ p1066) ∨ (¬ p1067) ∨ (¬ p1068)) : p1060 ∨ (¬ p1071) ∨ p1055 ∨ (¬ p1073) ∨ (¬ p1069) ∨ (¬ p1070) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1060) := fun hu => hn (Or.inl hu)
  have u1 : p1071 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1073 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1069 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1070 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1072) := by
    rcases h6258 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact q5
    · exact False.elim (q6 u3)
  have u7 : p1064 := by
    rcases h6326 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1065 := by
    rcases h6331 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1066 := by
    rcases h6336 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1067 := by
    rcases h6341 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1068 := by
    rcases h6346 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h6233 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22299 (p1055 p1060 p1069 p1070 p1071 p1073 : Prop)
    (h21538 : p1073 ∨ p1060 ∨ p1055)
    (h21539 : p1069 ∨ p1060 ∨ p1055)
    (h21540 : p1070 ∨ p1060 ∨ p1055)
    (h21541 : p1071 ∨ p1060 ∨ p1055)
    (h22298 : p1060 ∨ (¬ p1071) ∨ p1055 ∨ (¬ p1073) ∨ (¬ p1069) ∨ (¬ p1070)) : p1060 ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1060) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr hu)
  have u2 : p1073 := by
    rcases h21538 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1069 := by
    rcases h21539 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1070 := by
    rcases h21540 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1071 := by
    rcases h21541 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22298 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step22300 (p834 p840 p843 p848 p849 p850 p851 p852 : Prop)
    (h4895 : p843 ∨ p848)
    (h4896 : p843 ∨ p849)
    (h4897 : p843 ∨ p850)
    (h4898 : p843 ∨ p851)
    (h4899 : p843 ∨ p852)
    (h4822 : p834 ∨ p840 ∨ (¬ p848) ∨ (¬ p849) ∨ (¬ p850) ∨ (¬ p851) ∨ (¬ p852)) : p843 ∨ p834 ∨ p840 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p843) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p834) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p840) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p848 := by
    rcases h4895 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p849 := by
    rcases h4896 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p850 := by
    rcases h4897 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p851 := by
    rcases h4898 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p852 := by
    rcases h4899 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4822 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22301 (p834 p840 p847 p848 p849 p850 p851 p852 : Prop)
    (h4915 : p847 ∨ p848)
    (h4916 : p847 ∨ p849)
    (h4917 : p847 ∨ p850)
    (h4918 : p847 ∨ p851)
    (h4919 : p847 ∨ p852)
    (h4822 : p834 ∨ p840 ∨ (¬ p848) ∨ (¬ p849) ∨ (¬ p850) ∨ (¬ p851) ∨ (¬ p852)) : p847 ∨ p834 ∨ p840 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p847) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p834) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p840) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p848 := by
    rcases h4915 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p849 := by
    rcases h4916 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p850 := by
    rcases h4917 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p851 := by
    rcases h4918 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p852 := by
    rcases h4919 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4822 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22302 (p834 p840 p846 p848 p849 p850 p851 p852 : Prop)
    (h4910 : p846 ∨ p848)
    (h4911 : p846 ∨ p849)
    (h4912 : p846 ∨ p850)
    (h4913 : p846 ∨ p851)
    (h4914 : p846 ∨ p852)
    (h4822 : p834 ∨ p840 ∨ (¬ p848) ∨ (¬ p849) ∨ (¬ p850) ∨ (¬ p851) ∨ (¬ p852)) : p846 ∨ p834 ∨ p840 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p846) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p834) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p840) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p848 := by
    rcases h4910 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p849 := by
    rcases h4911 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p850 := by
    rcases h4912 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p851 := by
    rcases h4913 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p852 := by
    rcases h4914 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4822 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22303 (p834 p840 p845 p848 p849 p850 p851 p852 : Prop)
    (h4905 : p845 ∨ p848)
    (h4906 : p845 ∨ p849)
    (h4907 : p845 ∨ p850)
    (h4908 : p845 ∨ p851)
    (h4909 : p845 ∨ p852)
    (h4822 : p834 ∨ p840 ∨ (¬ p848) ∨ (¬ p849) ∨ (¬ p850) ∨ (¬ p851) ∨ (¬ p852)) : p845 ∨ p834 ∨ p840 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p845) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p834) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p840) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p848 := by
    rcases h4905 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p849 := by
    rcases h4906 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p850 := by
    rcases h4907 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p851 := by
    rcases h4908 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p852 := by
    rcases h4909 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4822 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22304 (p834 p840 p843 p844 p845 p846 p847 p848 p849 p850 p851 p852 : Prop)
    (h4797 : p834 ∨ p840 ∨ (¬ p843) ∨ (¬ p844) ∨ (¬ p845) ∨ (¬ p846) ∨ (¬ p847))
    (h4900 : p844 ∨ p848)
    (h4901 : p844 ∨ p849)
    (h4902 : p844 ∨ p850)
    (h4903 : p844 ∨ p851)
    (h4904 : p844 ∨ p852)
    (h4822 : p834 ∨ p840 ∨ (¬ p848) ∨ (¬ p849) ∨ (¬ p850) ∨ (¬ p851) ∨ (¬ p852)) : (¬ p845) ∨ (¬ p847) ∨ p840 ∨ p834 ∨ (¬ p846) ∨ (¬ p843) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p845 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p847 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p840) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p834) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p846 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p843 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p844) := by
    rcases h4797 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u5)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u1)
  have u7 : p848 := by
    rcases h4900 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p849 := by
    rcases h4901 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p850 := by
    rcases h4902 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p851 := by
    rcases h4903 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p852 := by
    rcases h4904 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h4822 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22305 (p834 p840 p843 p845 p846 p847 : Prop)
    (h22300 : p843 ∨ p834 ∨ p840)
    (h22301 : p847 ∨ p834 ∨ p840)
    (h22302 : p846 ∨ p834 ∨ p840)
    (h22303 : p845 ∨ p834 ∨ p840)
    (h22304 : (¬ p845) ∨ (¬ p847) ∨ p840 ∨ p834 ∨ (¬ p846) ∨ (¬ p843)) : p834 ∨ p840 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p834) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p840) := fun hu => hn (Or.inr hu)
  have u2 : p843 := by
    rcases h22300 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p847 := by
    rcases h22301 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p846 := by
    rcases h22302 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p845 := by
    rcases h22303 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22304 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u2)

theorem step22306 (p1074 p1095 p1314 p1319 p1320 p1321 p1322 p1323 : Prop)
    (h7940 : p1314 ∨ p1319)
    (h7941 : p1314 ∨ p1320)
    (h7942 : p1314 ∨ p1321)
    (h7943 : p1314 ∨ p1322)
    (h7944 : p1314 ∨ p1323)
    (h7877 : p1074 ∨ p1095 ∨ (¬ p1319) ∨ (¬ p1320) ∨ (¬ p1321) ∨ (¬ p1322) ∨ (¬ p1323)) : p1314 ∨ p1074 ∨ p1095 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1314) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1074) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1095) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1319 := by
    rcases h7940 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1320 := by
    rcases h7941 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1321 := by
    rcases h7942 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1322 := by
    rcases h7943 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1323 := by
    rcases h7944 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7877 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22307 (p1074 p1095 p1318 p1319 p1320 p1321 p1322 p1323 : Prop)
    (h7960 : p1318 ∨ p1319)
    (h7961 : p1318 ∨ p1320)
    (h7962 : p1318 ∨ p1321)
    (h7963 : p1318 ∨ p1322)
    (h7964 : p1318 ∨ p1323)
    (h7877 : p1074 ∨ p1095 ∨ (¬ p1319) ∨ (¬ p1320) ∨ (¬ p1321) ∨ (¬ p1322) ∨ (¬ p1323)) : p1318 ∨ p1074 ∨ p1095 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1318) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1074) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1095) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1319 := by
    rcases h7960 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1320 := by
    rcases h7961 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1321 := by
    rcases h7962 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1322 := by
    rcases h7963 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1323 := by
    rcases h7964 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7877 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22308 (p1074 p1095 p1317 p1319 p1320 p1321 p1322 p1323 : Prop)
    (h7955 : p1317 ∨ p1319)
    (h7956 : p1317 ∨ p1320)
    (h7957 : p1317 ∨ p1321)
    (h7958 : p1317 ∨ p1322)
    (h7959 : p1317 ∨ p1323)
    (h7877 : p1074 ∨ p1095 ∨ (¬ p1319) ∨ (¬ p1320) ∨ (¬ p1321) ∨ (¬ p1322) ∨ (¬ p1323)) : p1317 ∨ p1074 ∨ p1095 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1317) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1074) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1095) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1319 := by
    rcases h7955 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1320 := by
    rcases h7956 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1321 := by
    rcases h7957 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1322 := by
    rcases h7958 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1323 := by
    rcases h7959 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7877 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22309 (p1074 p1095 p1316 p1319 p1320 p1321 p1322 p1323 : Prop)
    (h7950 : p1316 ∨ p1319)
    (h7951 : p1316 ∨ p1320)
    (h7952 : p1316 ∨ p1321)
    (h7953 : p1316 ∨ p1322)
    (h7954 : p1316 ∨ p1323)
    (h7877 : p1074 ∨ p1095 ∨ (¬ p1319) ∨ (¬ p1320) ∨ (¬ p1321) ∨ (¬ p1322) ∨ (¬ p1323)) : p1316 ∨ p1074 ∨ p1095 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1316) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1074) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1095) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1319 := by
    rcases h7950 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1320 := by
    rcases h7951 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1321 := by
    rcases h7952 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1322 := by
    rcases h7953 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1323 := by
    rcases h7954 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7877 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22310 (p1074 p1095 p1314 p1315 p1316 p1317 p1318 p1319 p1320 p1321 p1322 p1323 : Prop)
    (h7852 : p1074 ∨ p1095 ∨ (¬ p1314) ∨ (¬ p1315) ∨ (¬ p1316) ∨ (¬ p1317) ∨ (¬ p1318))
    (h7945 : p1315 ∨ p1319)
    (h7946 : p1315 ∨ p1320)
    (h7947 : p1315 ∨ p1321)
    (h7948 : p1315 ∨ p1322)
    (h7949 : p1315 ∨ p1323)
    (h7877 : p1074 ∨ p1095 ∨ (¬ p1319) ∨ (¬ p1320) ∨ (¬ p1321) ∨ (¬ p1322) ∨ (¬ p1323)) : (¬ p1316) ∨ (¬ p1314) ∨ p1095 ∨ p1074 ∨ (¬ p1317) ∨ (¬ p1318) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1316 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1314 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1095) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1074) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1317 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1318 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1315) := by
    rcases h7852 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u1)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u5)
  have u7 : p1319 := by
    rcases h7945 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1320 := by
    rcases h7946 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1321 := by
    rcases h7947 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1322 := by
    rcases h7948 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1323 := by
    rcases h7949 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h7877 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22311 (p1074 p1095 p1314 p1316 p1317 p1318 : Prop)
    (h22306 : p1314 ∨ p1074 ∨ p1095)
    (h22307 : p1318 ∨ p1074 ∨ p1095)
    (h22308 : p1317 ∨ p1074 ∨ p1095)
    (h22309 : p1316 ∨ p1074 ∨ p1095)
    (h22310 : (¬ p1316) ∨ (¬ p1314) ∨ p1095 ∨ p1074 ∨ (¬ p1317) ∨ (¬ p1318)) : p1074 ∨ p1095 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1074) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1095) := fun hu => hn (Or.inr hu)
  have u2 : p1314 := by
    rcases h22306 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1318 := by
    rcases h22307 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1317 := by
    rcases h22308 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1316 := by
    rcases h22309 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22310 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22312 (p306 p350 p601 p634 p639 p1061 p1074 p1077 p1095 : Prop)
    (h13384 : (¬ p639) ∨ (¬ p1077) ∨ p1095)
    (h20840 : p639 ∨ p634)
    (h20360 : (¬ p306) ∨ (¬ p350) ∨ (¬ p601) ∨ (¬ p634) ∨ (¬ p1061) ∨ (¬ p1074))
    (h22311 : p1074 ∨ p1095) : p1095 ∨ (¬ p350) ∨ (¬ p1061) ∨ (¬ p306) ∨ (¬ p1077) ∨ (¬ p601) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1095) := fun hu => hn (Or.inl hu)
  have u1 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p639) := by
    rcases h13384 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u4)
    · exact False.elim (u0 q2)
  have u7 : p634 := by
    rcases h20840 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : (¬ p1074) := by
    rcases h20360 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u3)
    · exact False.elim (q1 u1)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u7)
    · exact False.elim (q4 u2)
    · exact q5
  rcases h22311 with q0 | q1
  · exact False.elim (u8 q0)
  · exact False.elim (u0 q1)

theorem step22313 (p238 p244 p249 p250 p251 p252 p253 p254 : Prop)
    (h1300 : p249 ∨ p250)
    (h1301 : p249 ∨ p251)
    (h1302 : p249 ∨ p252)
    (h1303 : p249 ∨ p253)
    (h1304 : p249 ∨ p254)
    (h1209 : p238 ∨ p244 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : p249 ∨ p238 ∨ p244 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p249) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p238) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p244) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p250 := by
    rcases h1300 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p251 := by
    rcases h1301 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p252 := by
    rcases h1302 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p253 := by
    rcases h1303 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p254 := by
    rcases h1304 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1209 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22314 (p238 p244 p248 p250 p251 p252 p253 p254 : Prop)
    (h1295 : p248 ∨ p250)
    (h1296 : p248 ∨ p251)
    (h1297 : p248 ∨ p252)
    (h1298 : p248 ∨ p253)
    (h1299 : p248 ∨ p254)
    (h1209 : p238 ∨ p244 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : p248 ∨ p238 ∨ p244 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p248) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p238) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p244) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p250 := by
    rcases h1295 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p251 := by
    rcases h1296 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p252 := by
    rcases h1297 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p253 := by
    rcases h1298 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p254 := by
    rcases h1299 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1209 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22315 (p238 p244 p247 p250 p251 p252 p253 p254 : Prop)
    (h1290 : p247 ∨ p250)
    (h1291 : p247 ∨ p251)
    (h1292 : p247 ∨ p252)
    (h1293 : p247 ∨ p253)
    (h1294 : p247 ∨ p254)
    (h1209 : p238 ∨ p244 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : p247 ∨ p238 ∨ p244 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p247) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p238) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p244) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p250 := by
    rcases h1290 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p251 := by
    rcases h1291 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p252 := by
    rcases h1292 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p253 := by
    rcases h1293 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p254 := by
    rcases h1294 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1209 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22316 (p238 p244 p246 p250 p251 p252 p253 p254 : Prop)
    (h1285 : p246 ∨ p250)
    (h1286 : p246 ∨ p251)
    (h1287 : p246 ∨ p252)
    (h1288 : p246 ∨ p253)
    (h1289 : p246 ∨ p254)
    (h1209 : p238 ∨ p244 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : p246 ∨ p238 ∨ p244 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p246) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p238) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p244) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p250 := by
    rcases h1285 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p251 := by
    rcases h1286 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p252 := by
    rcases h1287 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p253 := by
    rcases h1288 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p254 := by
    rcases h1289 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1209 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22317 (p238 p244 p245 p246 p247 p248 p249 p250 p251 p252 p253 p254 : Prop)
    (h1184 : p238 ∨ p244 ∨ (¬ p245) ∨ (¬ p246) ∨ (¬ p247) ∨ (¬ p248) ∨ (¬ p249))
    (h1280 : p245 ∨ p250)
    (h1281 : p245 ∨ p251)
    (h1282 : p245 ∨ p252)
    (h1283 : p245 ∨ p253)
    (h1284 : p245 ∨ p254)
    (h1209 : p238 ∨ p244 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : (¬ p246) ∨ (¬ p249) ∨ p244 ∨ (¬ p247) ∨ (¬ p248) ∨ p238 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p246 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p244) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p247 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p248 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p238) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p245) := by
    rcases h1184 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u5 q0)
    · exact False.elim (u2 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u1)
  have u7 : p250 := by
    rcases h1280 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p251 := by
    rcases h1281 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p252 := by
    rcases h1282 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p253 := by
    rcases h1283 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p254 := by
    rcases h1284 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h1209 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u5 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22318 (p238 p244 p246 p247 p248 p249 : Prop)
    (h22313 : p249 ∨ p238 ∨ p244)
    (h22314 : p248 ∨ p238 ∨ p244)
    (h22315 : p247 ∨ p238 ∨ p244)
    (h22316 : p246 ∨ p238 ∨ p244)
    (h22317 : (¬ p246) ∨ (¬ p249) ∨ p244 ∨ (¬ p247) ∨ (¬ p248) ∨ p238) : p238 ∨ p244 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p238) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p244) := fun hu => hn (Or.inr hu)
  have u2 : p249 := by
    rcases h22313 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p248 := by
    rcases h22314 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p247 := by
    rcases h22315 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p246 := by
    rcases h22316 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22317 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)
  · exact False.elim (u0 q5)

theorem step22319 (p158 p244 p245 p250 p251 p252 p253 p254 : Prop)
    (h1280 : p245 ∨ p250)
    (h1281 : p245 ∨ p251)
    (h1282 : p245 ∨ p252)
    (h1283 : p245 ∨ p253)
    (h1284 : p245 ∨ p254)
    (h1214 : p158 ∨ p244 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : p245 ∨ p244 ∨ p158 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p245) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p244) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p158) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p250 := by
    rcases h1280 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p251 := by
    rcases h1281 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p252 := by
    rcases h1282 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p253 := by
    rcases h1283 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p254 := by
    rcases h1284 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1214 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22320 (p158 p244 p249 p250 p251 p252 p253 p254 : Prop)
    (h1300 : p249 ∨ p250)
    (h1301 : p249 ∨ p251)
    (h1302 : p249 ∨ p252)
    (h1303 : p249 ∨ p253)
    (h1304 : p249 ∨ p254)
    (h1214 : p158 ∨ p244 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : p249 ∨ p244 ∨ p158 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p249) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p244) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p158) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p250 := by
    rcases h1300 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p251 := by
    rcases h1301 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p252 := by
    rcases h1302 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p253 := by
    rcases h1303 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p254 := by
    rcases h1304 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1214 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22321 (p158 p244 p248 p250 p251 p252 p253 p254 : Prop)
    (h1295 : p248 ∨ p250)
    (h1296 : p248 ∨ p251)
    (h1297 : p248 ∨ p252)
    (h1298 : p248 ∨ p253)
    (h1299 : p248 ∨ p254)
    (h1214 : p158 ∨ p244 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : p248 ∨ p244 ∨ p158 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p248) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p244) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p158) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p250 := by
    rcases h1295 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p251 := by
    rcases h1296 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p252 := by
    rcases h1297 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p253 := by
    rcases h1298 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p254 := by
    rcases h1299 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1214 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22322 (p158 p244 p247 p250 p251 p252 p253 p254 : Prop)
    (h1290 : p247 ∨ p250)
    (h1291 : p247 ∨ p251)
    (h1292 : p247 ∨ p252)
    (h1293 : p247 ∨ p253)
    (h1294 : p247 ∨ p254)
    (h1214 : p158 ∨ p244 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : p247 ∨ p244 ∨ p158 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p247) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p244) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p158) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p250 := by
    rcases h1290 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p251 := by
    rcases h1291 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p252 := by
    rcases h1292 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p253 := by
    rcases h1293 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p254 := by
    rcases h1294 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1214 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22323 (p158 p244 p245 p246 p247 p248 p249 p250 p251 p252 p253 p254 : Prop)
    (h1189 : p158 ∨ p244 ∨ (¬ p245) ∨ (¬ p246) ∨ (¬ p247) ∨ (¬ p248) ∨ (¬ p249))
    (h1285 : p246 ∨ p250)
    (h1286 : p246 ∨ p251)
    (h1287 : p246 ∨ p252)
    (h1288 : p246 ∨ p253)
    (h1289 : p246 ∨ p254)
    (h1214 : p158 ∨ p244 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254)) : (¬ p247) ∨ (¬ p249) ∨ p158 ∨ p244 ∨ (¬ p248) ∨ (¬ p245) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p247 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p158) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p244) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p248 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p245 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p246) := by
    rcases h1189 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u5)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u1)
  have u7 : p250 := by
    rcases h1285 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p251 := by
    rcases h1286 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p252 := by
    rcases h1287 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p253 := by
    rcases h1288 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p254 := by
    rcases h1289 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h1214 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22324 (p158 p244 p245 p247 p248 p249 : Prop)
    (h22319 : p245 ∨ p244 ∨ p158)
    (h22320 : p249 ∨ p244 ∨ p158)
    (h22321 : p248 ∨ p244 ∨ p158)
    (h22322 : p247 ∨ p244 ∨ p158)
    (h22323 : (¬ p247) ∨ (¬ p249) ∨ p158 ∨ p244 ∨ (¬ p248) ∨ (¬ p245)) : p244 ∨ p158 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p244) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p158) := fun hu => hn (Or.inr hu)
  have u2 : p245 := by
    rcases h22319 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p249 := by
    rcases h22320 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p248 := by
    rcases h22321 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p247 := by
    rcases h22322 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22323 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u2)

theorem step22328 (p2 p5 p344 p419 p499 p633 p657 p665 p1077 : Prop)
    (h18249 : (¬ p2) ∨ (¬ p5) ∨ (¬ p419) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p665) ∨ (¬ p1077))
    (h17477 : (¬ p344) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p657))
    (h22069 : p665 ∨ p657) : (¬ p633) ∨ (¬ p499) ∨ (¬ p419) ∨ (¬ p344) ∨ (¬ p1077) ∨ (¬ p5) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p665) := by
    rcases h18249 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u6)
    · exact False.elim (q1 u5)
    · exact False.elim (q2 u2)
    · exact False.elim (q3 u1)
    · exact False.elim (q4 u0)
    · exact q5
    · exact False.elim (q6 u4)
  have u8 : (¬ p657) := by
    rcases h17477 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u3)
    · exact False.elim (q1 u1)
    · exact False.elim (q2 u0)
    · exact q3
  rcases h22069 with q0 | q1
  · exact False.elim (u7 q0)
  · exact False.elim (u8 q1)

theorem step22339 (p425 p494 p506 p507 p508 p509 p510 p511 : Prop)
    (h2847 : p506 ∨ p507)
    (h2848 : p506 ∨ p508)
    (h2849 : p506 ∨ p509)
    (h2850 : p506 ∨ p510)
    (h2851 : p506 ∨ p511)
    (h2752 : p425 ∨ p494 ∨ (¬ p507) ∨ (¬ p508) ∨ (¬ p509) ∨ (¬ p510) ∨ (¬ p511)) : p506 ∨ p425 ∨ p494 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p506) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p425) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p494) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p507 := by
    rcases h2847 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p508 := by
    rcases h2848 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p509 := by
    rcases h2849 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p510 := by
    rcases h2850 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p511 := by
    rcases h2851 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2752 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22340 (p425 p494 p505 p507 p508 p509 p510 p511 : Prop)
    (h2842 : p505 ∨ p507)
    (h2843 : p505 ∨ p508)
    (h2844 : p505 ∨ p509)
    (h2845 : p505 ∨ p510)
    (h2846 : p505 ∨ p511)
    (h2752 : p425 ∨ p494 ∨ (¬ p507) ∨ (¬ p508) ∨ (¬ p509) ∨ (¬ p510) ∨ (¬ p511)) : p505 ∨ p425 ∨ p494 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p505) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p425) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p494) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p507 := by
    rcases h2842 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p508 := by
    rcases h2843 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p509 := by
    rcases h2844 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p510 := by
    rcases h2845 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p511 := by
    rcases h2846 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2752 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22341 (p425 p494 p504 p507 p508 p509 p510 p511 : Prop)
    (h2837 : p504 ∨ p507)
    (h2838 : p504 ∨ p508)
    (h2839 : p504 ∨ p509)
    (h2840 : p504 ∨ p510)
    (h2841 : p504 ∨ p511)
    (h2752 : p425 ∨ p494 ∨ (¬ p507) ∨ (¬ p508) ∨ (¬ p509) ∨ (¬ p510) ∨ (¬ p511)) : p504 ∨ p425 ∨ p494 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p504) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p425) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p494) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p507 := by
    rcases h2837 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p508 := by
    rcases h2838 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p509 := by
    rcases h2839 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p510 := by
    rcases h2840 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p511 := by
    rcases h2841 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2752 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22342 (p425 p494 p503 p507 p508 p509 p510 p511 : Prop)
    (h2832 : p503 ∨ p507)
    (h2833 : p503 ∨ p508)
    (h2834 : p503 ∨ p509)
    (h2835 : p503 ∨ p510)
    (h2836 : p503 ∨ p511)
    (h2752 : p425 ∨ p494 ∨ (¬ p507) ∨ (¬ p508) ∨ (¬ p509) ∨ (¬ p510) ∨ (¬ p511)) : p503 ∨ p425 ∨ p494 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p503) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p425) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p494) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p507 := by
    rcases h2832 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p508 := by
    rcases h2833 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p509 := by
    rcases h2834 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p510 := by
    rcases h2835 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p511 := by
    rcases h2836 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2752 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22343 (p425 p494 p502 p503 p504 p505 p506 p507 p508 p509 p510 p511 : Prop)
    (h2727 : p425 ∨ p494 ∨ (¬ p502) ∨ (¬ p503) ∨ (¬ p504) ∨ (¬ p505) ∨ (¬ p506))
    (h2827 : p502 ∨ p507)
    (h2828 : p502 ∨ p508)
    (h2829 : p502 ∨ p509)
    (h2830 : p502 ∨ p510)
    (h2831 : p502 ∨ p511)
    (h2752 : p425 ∨ p494 ∨ (¬ p507) ∨ (¬ p508) ∨ (¬ p509) ∨ (¬ p510) ∨ (¬ p511)) : (¬ p503) ∨ p425 ∨ p494 ∨ (¬ p506) ∨ (¬ p504) ∨ (¬ p505) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p503 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p425) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p494) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p506 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p504 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p505 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p502) := by
    rcases h2727 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u2 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u3)
  have u7 : p507 := by
    rcases h2827 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p508 := by
    rcases h2828 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p509 := by
    rcases h2829 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p510 := by
    rcases h2830 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p511 := by
    rcases h2831 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h2752 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22344 (p425 p494 p503 p504 p505 p506 : Prop)
    (h22339 : p506 ∨ p425 ∨ p494)
    (h22340 : p505 ∨ p425 ∨ p494)
    (h22341 : p504 ∨ p425 ∨ p494)
    (h22342 : p503 ∨ p425 ∨ p494)
    (h22343 : (¬ p503) ∨ p425 ∨ p494 ∨ (¬ p506) ∨ (¬ p504) ∨ (¬ p505)) : p425 ∨ p494 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p425) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p494) := fun hu => hn (Or.inr hu)
  have u2 : p506 := by
    rcases h22339 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p505 := by
    rcases h22340 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p504 := by
    rcases h22341 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p503 := by
    rcases h22342 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22343 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22345 (p1385 p1393 p1400 p1401 p1402 p1403 p1404 p1405 : Prop)
    (h8469 : p1400 ∨ p1401)
    (h8470 : p1400 ∨ p1402)
    (h8471 : p1400 ∨ p1403)
    (h8472 : p1400 ∨ p1404)
    (h8473 : p1400 ∨ p1405)
    (h8386 : p1385 ∨ p1393 ∨ (¬ p1401) ∨ (¬ p1402) ∨ (¬ p1403) ∨ (¬ p1404) ∨ (¬ p1405)) : p1400 ∨ p1385 ∨ p1393 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1400) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1385) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1393) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1401 := by
    rcases h8469 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1402 := by
    rcases h8470 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1403 := by
    rcases h8471 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1404 := by
    rcases h8472 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1405 := by
    rcases h8473 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8386 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22346 (p1385 p1393 p1399 p1401 p1402 p1403 p1404 p1405 : Prop)
    (h8464 : p1399 ∨ p1401)
    (h8465 : p1399 ∨ p1402)
    (h8466 : p1399 ∨ p1403)
    (h8467 : p1399 ∨ p1404)
    (h8468 : p1399 ∨ p1405)
    (h8386 : p1385 ∨ p1393 ∨ (¬ p1401) ∨ (¬ p1402) ∨ (¬ p1403) ∨ (¬ p1404) ∨ (¬ p1405)) : p1399 ∨ p1385 ∨ p1393 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1399) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1385) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1393) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1401 := by
    rcases h8464 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1402 := by
    rcases h8465 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1403 := by
    rcases h8466 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1404 := by
    rcases h8467 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1405 := by
    rcases h8468 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8386 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22347 (p1385 p1393 p1398 p1401 p1402 p1403 p1404 p1405 : Prop)
    (h8459 : p1398 ∨ p1401)
    (h8460 : p1398 ∨ p1402)
    (h8461 : p1398 ∨ p1403)
    (h8462 : p1398 ∨ p1404)
    (h8463 : p1398 ∨ p1405)
    (h8386 : p1385 ∨ p1393 ∨ (¬ p1401) ∨ (¬ p1402) ∨ (¬ p1403) ∨ (¬ p1404) ∨ (¬ p1405)) : p1398 ∨ p1385 ∨ p1393 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1398) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1385) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1393) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1401 := by
    rcases h8459 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1402 := by
    rcases h8460 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1403 := by
    rcases h8461 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1404 := by
    rcases h8462 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1405 := by
    rcases h8463 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8386 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22348 (p1385 p1393 p1397 p1401 p1402 p1403 p1404 p1405 : Prop)
    (h8454 : p1397 ∨ p1401)
    (h8455 : p1397 ∨ p1402)
    (h8456 : p1397 ∨ p1403)
    (h8457 : p1397 ∨ p1404)
    (h8458 : p1397 ∨ p1405)
    (h8386 : p1385 ∨ p1393 ∨ (¬ p1401) ∨ (¬ p1402) ∨ (¬ p1403) ∨ (¬ p1404) ∨ (¬ p1405)) : p1397 ∨ p1385 ∨ p1393 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1397) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1385) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1393) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1401 := by
    rcases h8454 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1402 := by
    rcases h8455 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1403 := by
    rcases h8456 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1404 := by
    rcases h8457 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1405 := by
    rcases h8458 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8386 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22349 (p1385 p1393 p1396 p1397 p1398 p1399 p1400 p1401 p1402 p1403 p1404 p1405 : Prop)
    (h8361 : p1385 ∨ p1393 ∨ (¬ p1396) ∨ (¬ p1397) ∨ (¬ p1398) ∨ (¬ p1399) ∨ (¬ p1400))
    (h8449 : p1396 ∨ p1401)
    (h8450 : p1396 ∨ p1402)
    (h8451 : p1396 ∨ p1403)
    (h8452 : p1396 ∨ p1404)
    (h8453 : p1396 ∨ p1405)
    (h8386 : p1385 ∨ p1393 ∨ (¬ p1401) ∨ (¬ p1402) ∨ (¬ p1403) ∨ (¬ p1404) ∨ (¬ p1405)) : (¬ p1397) ∨ (¬ p1400) ∨ p1385 ∨ p1393 ∨ (¬ p1398) ∨ (¬ p1399) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1397 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1400 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1393) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1398 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1399 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1396) := by
    rcases h8361 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p1401 := by
    rcases h8449 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1402 := by
    rcases h8450 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1403 := by
    rcases h8451 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1404 := by
    rcases h8452 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1405 := by
    rcases h8453 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h8386 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22350 (p1385 p1393 p1397 p1398 p1399 p1400 : Prop)
    (h22345 : p1400 ∨ p1385 ∨ p1393)
    (h22346 : p1399 ∨ p1385 ∨ p1393)
    (h22347 : p1398 ∨ p1385 ∨ p1393)
    (h22348 : p1397 ∨ p1385 ∨ p1393)
    (h22349 : (¬ p1397) ∨ (¬ p1400) ∨ p1385 ∨ p1393 ∨ (¬ p1398) ∨ (¬ p1399)) : p1385 ∨ p1393 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1385) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1393) := fun hu => hn (Or.inr hu)
  have u2 : p1400 := by
    rcases h22345 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1399 := by
    rcases h22346 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1398 := by
    rcases h22347 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1397 := by
    rcases h22348 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22349 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22352 (p237 p657 p789 p833 p834 p918 p1385 p1393 : Prop)
    (h15808 : (¬ p834) ∨ (¬ p918) ∨ p1385)
    (h22350 : p1385 ∨ p1393)
    (h22217 : p834 ∨ p833)
    (h20568 : (¬ p237) ∨ (¬ p789) ∨ (¬ p918) ∨ (¬ p1393))
    (h15123 : (¬ p657) ∨ p789 ∨ (¬ p833)) : p1385 ∨ (¬ p918) ∨ (¬ p237) ∨ (¬ p657) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1385) := fun hu => hn (Or.inl hu)
  have u1 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p834) := by
    rcases h15808 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u1)
    · exact False.elim (u0 q2)
  have u5 : p1393 := by
    rcases h22350 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p833 := by
    rcases h22217 with q0 | q1
    · exact False.elim (u4 q0)
    · exact q1
  have u7 : (¬ p789) := by
    rcases h20568 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u2)
    · exact q1
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u5)
  rcases h15123 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u6)

theorem step22354 (p344 p455 p634 p639 p897 p904 p1084 : Prop)
    (h20784 : p897 ∨ p904)
    (h13391 : (¬ p344) ∨ (¬ p639) ∨ p904)
    (h16495 : (¬ p344) ∨ (¬ p455) ∨ (¬ p634) ∨ (¬ p897) ∨ (¬ p1084))
    (h20840 : p639 ∨ p634) : p904 ∨ (¬ p1084) ∨ (¬ p455) ∨ (¬ p344) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p904) := fun hu => hn (Or.inl hu)
  have u1 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p897 := by
    rcases h20784 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : (¬ p639) := by
    rcases h13391 with q0 | q1 | q2
    · exact False.elim (q0 u3)
    · exact q1
    · exact False.elim (u0 q2)
  have u6 : (¬ p634) := by
    rcases h16495 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u3)
    · exact False.elim (q1 u2)
    · exact q2
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u1)
  rcases h20840 with q0 | q1
  · exact False.elim (u5 q0)
  · exact False.elim (u6 q1)

theorem step22356 (p224 p667 p671 p675 p676 p677 p678 p679 : Prop)
    (h3864 : p671 ∨ p675)
    (h3865 : p671 ∨ p676)
    (h3866 : p671 ∨ p677)
    (h3867 : p671 ∨ p678)
    (h3868 : p671 ∨ p679)
    (h3795 : p224 ∨ p667 ∨ (¬ p675) ∨ (¬ p676) ∨ (¬ p677) ∨ (¬ p678) ∨ (¬ p679)) : p671 ∨ p667 ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p671) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p667) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p675 := by
    rcases h3864 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p676 := by
    rcases h3865 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p677 := by
    rcases h3866 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p678 := by
    rcases h3867 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p679 := by
    rcases h3868 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3795 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22357 (p224 p667 p670 p675 p676 p677 p678 p679 : Prop)
    (h3859 : p670 ∨ p675)
    (h3860 : p670 ∨ p676)
    (h3861 : p670 ∨ p677)
    (h3862 : p670 ∨ p678)
    (h3863 : p670 ∨ p679)
    (h3795 : p224 ∨ p667 ∨ (¬ p675) ∨ (¬ p676) ∨ (¬ p677) ∨ (¬ p678) ∨ (¬ p679)) : p670 ∨ p667 ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p670) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p667) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p675 := by
    rcases h3859 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p676 := by
    rcases h3860 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p677 := by
    rcases h3861 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p678 := by
    rcases h3862 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p679 := by
    rcases h3863 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3795 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22358 (p224 p667 p674 p675 p676 p677 p678 p679 : Prop)
    (h3879 : p674 ∨ p675)
    (h3880 : p674 ∨ p676)
    (h3881 : p674 ∨ p677)
    (h3882 : p674 ∨ p678)
    (h3883 : p674 ∨ p679)
    (h3795 : p224 ∨ p667 ∨ (¬ p675) ∨ (¬ p676) ∨ (¬ p677) ∨ (¬ p678) ∨ (¬ p679)) : p674 ∨ p667 ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p674) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p667) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p675 := by
    rcases h3879 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p676 := by
    rcases h3880 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p677 := by
    rcases h3881 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p678 := by
    rcases h3882 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p679 := by
    rcases h3883 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3795 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22359 (p224 p667 p673 p675 p676 p677 p678 p679 : Prop)
    (h3874 : p673 ∨ p675)
    (h3875 : p673 ∨ p676)
    (h3876 : p673 ∨ p677)
    (h3877 : p673 ∨ p678)
    (h3878 : p673 ∨ p679)
    (h3795 : p224 ∨ p667 ∨ (¬ p675) ∨ (¬ p676) ∨ (¬ p677) ∨ (¬ p678) ∨ (¬ p679)) : p673 ∨ p667 ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p673) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p667) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p675 := by
    rcases h3874 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p676 := by
    rcases h3875 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p677 := by
    rcases h3876 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p678 := by
    rcases h3877 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p679 := by
    rcases h3878 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3795 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22360 (p224 p667 p670 p671 p672 p673 p674 p675 p676 p677 p678 p679 : Prop)
    (h3770 : p224 ∨ p667 ∨ (¬ p670) ∨ (¬ p671) ∨ (¬ p672) ∨ (¬ p673) ∨ (¬ p674))
    (h3869 : p672 ∨ p675)
    (h3870 : p672 ∨ p676)
    (h3871 : p672 ∨ p677)
    (h3872 : p672 ∨ p678)
    (h3873 : p672 ∨ p679)
    (h3795 : p224 ∨ p667 ∨ (¬ p675) ∨ (¬ p676) ∨ (¬ p677) ∨ (¬ p678) ∨ (¬ p679)) : (¬ p673) ∨ (¬ p674) ∨ p224 ∨ p667 ∨ (¬ p670) ∨ (¬ p671) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p673 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p674 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p667) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p670 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p671 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p672) := by
    rcases h3770 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact q4
    · exact False.elim (q5 u0)
    · exact False.elim (q6 u1)
  have u7 : p675 := by
    rcases h3869 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p676 := by
    rcases h3870 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p677 := by
    rcases h3871 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p678 := by
    rcases h3872 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p679 := by
    rcases h3873 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h3795 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22361 (p224 p667 p670 p671 p673 p674 : Prop)
    (h22356 : p671 ∨ p667 ∨ p224)
    (h22357 : p670 ∨ p667 ∨ p224)
    (h22358 : p674 ∨ p667 ∨ p224)
    (h22359 : p673 ∨ p667 ∨ p224)
    (h22360 : (¬ p673) ∨ (¬ p674) ∨ p224 ∨ p667 ∨ (¬ p670) ∨ (¬ p671)) : p667 ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p667) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr hu)
  have u2 : p671 := by
    rcases h22356 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p670 := by
    rcases h22357 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p674 := by
    rcases h22358 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p673 := by
    rcases h22359 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22360 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u2)

theorem step22362 (p431 p1332 p1340 p1341 p1342 p1343 p1344 p1345 : Prop)
    (h8092 : p1340 ∨ p1341)
    (h8093 : p1340 ∨ p1342)
    (h8094 : p1340 ∨ p1343)
    (h8095 : p1340 ∨ p1344)
    (h8096 : p1340 ∨ p1345)
    (h8013 : p431 ∨ p1332 ∨ (¬ p1341) ∨ (¬ p1342) ∨ (¬ p1343) ∨ (¬ p1344) ∨ (¬ p1345)) : p1340 ∨ p431 ∨ p1332 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1340) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p431) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1332) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h8013 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22363 (p431 p1332 p1336 p1341 p1342 p1343 p1344 p1345 : Prop)
    (h8072 : p1336 ∨ p1341)
    (h8073 : p1336 ∨ p1342)
    (h8074 : p1336 ∨ p1343)
    (h8075 : p1336 ∨ p1344)
    (h8076 : p1336 ∨ p1345)
    (h8013 : p431 ∨ p1332 ∨ (¬ p1341) ∨ (¬ p1342) ∨ (¬ p1343) ∨ (¬ p1344) ∨ (¬ p1345)) : p1336 ∨ p431 ∨ p1332 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1336) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p431) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1332) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h8013 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22364 (p431 p1332 p1339 p1341 p1342 p1343 p1344 p1345 : Prop)
    (h8087 : p1339 ∨ p1341)
    (h8088 : p1339 ∨ p1342)
    (h8089 : p1339 ∨ p1343)
    (h8090 : p1339 ∨ p1344)
    (h8091 : p1339 ∨ p1345)
    (h8013 : p431 ∨ p1332 ∨ (¬ p1341) ∨ (¬ p1342) ∨ (¬ p1343) ∨ (¬ p1344) ∨ (¬ p1345)) : p1339 ∨ p431 ∨ p1332 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1339) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p431) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1332) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h8013 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22365 (p431 p1332 p1338 p1341 p1342 p1343 p1344 p1345 : Prop)
    (h8082 : p1338 ∨ p1341)
    (h8083 : p1338 ∨ p1342)
    (h8084 : p1338 ∨ p1343)
    (h8085 : p1338 ∨ p1344)
    (h8086 : p1338 ∨ p1345)
    (h8013 : p431 ∨ p1332 ∨ (¬ p1341) ∨ (¬ p1342) ∨ (¬ p1343) ∨ (¬ p1344) ∨ (¬ p1345)) : p1338 ∨ p431 ∨ p1332 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1338) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p431) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1332) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h8013 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22366 (p431 p1332 p1336 p1337 p1338 p1339 p1340 p1341 p1342 p1343 p1344 p1345 : Prop)
    (h7988 : p431 ∨ p1332 ∨ (¬ p1336) ∨ (¬ p1337) ∨ (¬ p1338) ∨ (¬ p1339) ∨ (¬ p1340))
    (h8077 : p1337 ∨ p1341)
    (h8078 : p1337 ∨ p1342)
    (h8079 : p1337 ∨ p1343)
    (h8080 : p1337 ∨ p1344)
    (h8081 : p1337 ∨ p1345)
    (h8013 : p431 ∨ p1332 ∨ (¬ p1341) ∨ (¬ p1342) ∨ (¬ p1343) ∨ (¬ p1344) ∨ (¬ p1345)) : (¬ p1338) ∨ (¬ p1340) ∨ p1332 ∨ p431 ∨ (¬ p1339) ∨ (¬ p1336) := by
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
  have u2 : (¬ p1332) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p431) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1339 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1336 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1337) := by
    rcases h7988 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u5)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u1)
  have u7 : p1341 := by
    rcases h8077 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1342 := by
    rcases h8078 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1343 := by
    rcases h8079 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1344 := by
    rcases h8080 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1345 := by
    rcases h8081 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h8013 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22367 (p431 p1332 p1336 p1338 p1339 p1340 : Prop)
    (h22362 : p1340 ∨ p431 ∨ p1332)
    (h22363 : p1336 ∨ p431 ∨ p1332)
    (h22364 : p1339 ∨ p431 ∨ p1332)
    (h22365 : p1338 ∨ p431 ∨ p1332)
    (h22366 : (¬ p1338) ∨ (¬ p1340) ∨ p1332 ∨ p431 ∨ (¬ p1339) ∨ (¬ p1336)) : p431 ∨ p1332 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p431) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1332) := fun hu => hn (Or.inr hu)
  have u2 : p1340 := by
    rcases h22362 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1336 := by
    rcases h22363 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1339 := by
    rcases h22364 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1338 := by
    rcases h22365 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22366 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22368 (p8 p15 p49 p84 p242 p431 p435 p595 p616 p657 p996 p1189 p1193 p1332 p1545 : Prop)
    (h10651 : (¬ p595) ∨ (¬ p616))
    (h9388 : (¬ p15) ∨ p595 ∨ (¬ p1193))
    (h21784 : p1189 ∨ p1193)
    (h11138 : (¬ p435) ∨ (¬ p996) ∨ (¬ p1332))
    (h10672 : (¬ p435) ∨ (¬ p1189) ∨ p1545)
    (h19697 : (¬ p8) ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p242) ∨ (¬ p431) ∨ (¬ p616) ∨ (¬ p657) ∨ (¬ p1545))
    (h22367 : p431 ∨ p1332) : (¬ p435) ∨ (¬ p616) ∨ (¬ p242) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p657) ∨ (¬ p996) ∨ (¬ p15) ∨ (¬ p8) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p595) := by
    rcases h10651 with q0 | q1
    · exact q0
    · exact False.elim (q1 u1)
  have u10 : (¬ p1193) := by
    rcases h9388 with q0 | q1 | q2
    · exact False.elim (q0 u7)
    · exact False.elim (u9 q1)
    · exact q2
  have u11 : p1189 := by
    rcases h21784 with q0 | q1
    · exact q0
    · exact False.elim (u10 q1)
  have u12 : (¬ p1332) := by
    rcases h11138 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact False.elim (q1 u6)
    · exact q2
  have u13 : p1545 := by
    rcases h10672 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact False.elim (q1 u11)
    · exact q2
  have u14 : (¬ p431) := by
    rcases h19697 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
    · exact False.elim (q0 u8)
    · exact False.elim (q1 u7)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u2)
    · exact q5
    · exact False.elim (q6 u1)
    · exact False.elim (q7 u5)
    · exact False.elim (q8 u13)
  rcases h22367 with q0 | q1
  · exact False.elim (u14 q0)
  · exact False.elim (u12 q1)

theorem step22369 (p1229 p1232 p1243 p1247 : Prop)
    (h7451 : p1243 ∨ p1247)
    (h21803 : p1243 ∨ (¬ p1247) ∨ p1229 ∨ p1232) : p1243 ∨ p1229 ∨ p1232 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1243) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1232) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1247 := by
    rcases h7451 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h21803 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (u1 q2)
  · exact False.elim (u2 q3)

theorem step22370 (p1229 p1232 p1242 p1244 p1245 p1246 p1247 p1248 : Prop)
    (h7443 : p1242 ∨ p1244)
    (h7444 : p1242 ∨ p1245)
    (h7445 : p1242 ∨ p1246)
    (h7446 : p1242 ∨ p1247)
    (h7447 : p1242 ∨ p1248)
    (h7365 : p1229 ∨ p1232 ∨ (¬ p1244) ∨ (¬ p1245) ∨ (¬ p1246) ∨ (¬ p1247) ∨ (¬ p1248)) : p1242 ∨ p1229 ∨ p1232 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1242) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1232) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1244 := by
    rcases h7443 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1245 := by
    rcases h7444 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1246 := by
    rcases h7445 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1247 := by
    rcases h7446 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1248 := by
    rcases h7447 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7365 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22371 (p1229 p1232 p1241 p1244 p1245 p1246 p1247 p1248 : Prop)
    (h7438 : p1241 ∨ p1244)
    (h7439 : p1241 ∨ p1245)
    (h7440 : p1241 ∨ p1246)
    (h7441 : p1241 ∨ p1247)
    (h7442 : p1241 ∨ p1248)
    (h7365 : p1229 ∨ p1232 ∨ (¬ p1244) ∨ (¬ p1245) ∨ (¬ p1246) ∨ (¬ p1247) ∨ (¬ p1248)) : p1241 ∨ p1229 ∨ p1232 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1241) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1232) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1244 := by
    rcases h7438 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1245 := by
    rcases h7439 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1246 := by
    rcases h7440 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1247 := by
    rcases h7441 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1248 := by
    rcases h7442 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7365 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22372 (p1229 p1232 p1240 p1244 p1245 p1246 p1247 p1248 : Prop)
    (h7433 : p1240 ∨ p1244)
    (h7434 : p1240 ∨ p1245)
    (h7435 : p1240 ∨ p1246)
    (h7436 : p1240 ∨ p1247)
    (h7437 : p1240 ∨ p1248)
    (h7365 : p1229 ∨ p1232 ∨ (¬ p1244) ∨ (¬ p1245) ∨ (¬ p1246) ∨ (¬ p1247) ∨ (¬ p1248)) : p1240 ∨ p1229 ∨ p1232 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1240) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1232) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1244 := by
    rcases h7433 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1245 := by
    rcases h7434 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1246 := by
    rcases h7435 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1247 := by
    rcases h7436 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1248 := by
    rcases h7437 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7365 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22373 (p1229 p1232 p1239 p1240 p1241 p1242 p1243 p1244 p1245 p1246 p1247 p1248 : Prop)
    (h7340 : p1229 ∨ p1232 ∨ (¬ p1239) ∨ (¬ p1240) ∨ (¬ p1241) ∨ (¬ p1242) ∨ (¬ p1243))
    (h7428 : p1239 ∨ p1244)
    (h7429 : p1239 ∨ p1245)
    (h7430 : p1239 ∨ p1246)
    (h7431 : p1239 ∨ p1247)
    (h7432 : p1239 ∨ p1248)
    (h7365 : p1229 ∨ p1232 ∨ (¬ p1244) ∨ (¬ p1245) ∨ (¬ p1246) ∨ (¬ p1247) ∨ (¬ p1248)) : (¬ p1240) ∨ (¬ p1243) ∨ p1232 ∨ p1229 ∨ (¬ p1241) ∨ (¬ p1242) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1240 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1243 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1232) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1239) := by
    rcases h7340 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p1244 := by
    rcases h7428 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1245 := by
    rcases h7429 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1246 := by
    rcases h7430 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1247 := by
    rcases h7431 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1248 := by
    rcases h7432 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h7365 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22374 (p1229 p1232 p1240 p1241 p1242 p1243 : Prop)
    (h22369 : p1243 ∨ p1229 ∨ p1232)
    (h22370 : p1242 ∨ p1229 ∨ p1232)
    (h22371 : p1241 ∨ p1229 ∨ p1232)
    (h22372 : p1240 ∨ p1229 ∨ p1232)
    (h22373 : (¬ p1240) ∨ (¬ p1243) ∨ p1232 ∨ p1229 ∨ (¬ p1241) ∨ (¬ p1242)) : p1229 ∨ p1232 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1229) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1232) := fun hu => hn (Or.inr hu)
  have u2 : p1243 := by
    rcases h22369 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1242 := by
    rcases h22370 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1241 := by
    rcases h22371 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1240 := by
    rcases h22372 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22373 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22375 (p457 p461 p465 p470 p471 p472 p473 p474 : Prop)
    (h2575 : p465 ∨ p470)
    (h2576 : p465 ∨ p471)
    (h2577 : p465 ∨ p472)
    (h2578 : p465 ∨ p473)
    (h2579 : p465 ∨ p474)
    (h2500 : p457 ∨ p461 ∨ (¬ p470) ∨ (¬ p471) ∨ (¬ p472) ∨ (¬ p473) ∨ (¬ p474)) : p465 ∨ p461 ∨ p457 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p465) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p461) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p457) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p470 := by
    rcases h2575 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p471 := by
    rcases h2576 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p472 := by
    rcases h2577 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p473 := by
    rcases h2578 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p474 := by
    rcases h2579 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2500 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22376 (p457 p461 p469 p470 p471 p472 p473 p474 : Prop)
    (h2595 : p469 ∨ p470)
    (h2596 : p469 ∨ p471)
    (h2597 : p469 ∨ p472)
    (h2598 : p469 ∨ p473)
    (h2599 : p469 ∨ p474)
    (h2500 : p457 ∨ p461 ∨ (¬ p470) ∨ (¬ p471) ∨ (¬ p472) ∨ (¬ p473) ∨ (¬ p474)) : p469 ∨ p461 ∨ p457 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p469) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p461) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p457) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p470 := by
    rcases h2595 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p471 := by
    rcases h2596 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p472 := by
    rcases h2597 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p473 := by
    rcases h2598 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p474 := by
    rcases h2599 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2500 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22377 (p457 p461 p468 p470 p471 p472 p473 p474 : Prop)
    (h2590 : p468 ∨ p470)
    (h2591 : p468 ∨ p471)
    (h2592 : p468 ∨ p472)
    (h2593 : p468 ∨ p473)
    (h2594 : p468 ∨ p474)
    (h2500 : p457 ∨ p461 ∨ (¬ p470) ∨ (¬ p471) ∨ (¬ p472) ∨ (¬ p473) ∨ (¬ p474)) : p468 ∨ p461 ∨ p457 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p468) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p461) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p457) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p470 := by
    rcases h2590 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p471 := by
    rcases h2591 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p472 := by
    rcases h2592 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p473 := by
    rcases h2593 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p474 := by
    rcases h2594 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2500 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22378 (p457 p461 p467 p470 p471 p472 p473 p474 : Prop)
    (h2585 : p467 ∨ p470)
    (h2586 : p467 ∨ p471)
    (h2587 : p467 ∨ p472)
    (h2588 : p467 ∨ p473)
    (h2589 : p467 ∨ p474)
    (h2500 : p457 ∨ p461 ∨ (¬ p470) ∨ (¬ p471) ∨ (¬ p472) ∨ (¬ p473) ∨ (¬ p474)) : p467 ∨ p461 ∨ p457 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p467) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p461) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p457) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p470 := by
    rcases h2585 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p471 := by
    rcases h2586 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p472 := by
    rcases h2587 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p473 := by
    rcases h2588 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p474 := by
    rcases h2589 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2500 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22379 (p457 p461 p465 p466 p467 p468 p469 p470 p471 p472 p473 p474 : Prop)
    (h2475 : p457 ∨ p461 ∨ (¬ p465) ∨ (¬ p466) ∨ (¬ p467) ∨ (¬ p468) ∨ (¬ p469))
    (h2580 : p466 ∨ p470)
    (h2581 : p466 ∨ p471)
    (h2582 : p466 ∨ p472)
    (h2583 : p466 ∨ p473)
    (h2584 : p466 ∨ p474)
    (h2500 : p457 ∨ p461 ∨ (¬ p470) ∨ (¬ p471) ∨ (¬ p472) ∨ (¬ p473) ∨ (¬ p474)) : (¬ p467) ∨ p457 ∨ p461 ∨ (¬ p468) ∨ (¬ p469) ∨ (¬ p465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p467 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p457) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p461) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p468 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p469 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p466) := by
    rcases h2475 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u5)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u3)
    · exact False.elim (q6 u4)
  have u7 : p470 := by
    rcases h2580 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p471 := by
    rcases h2581 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p472 := by
    rcases h2582 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p473 := by
    rcases h2583 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p474 := by
    rcases h2584 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h2500 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22380 (p457 p461 p465 p467 p468 p469 : Prop)
    (h22375 : p465 ∨ p461 ∨ p457)
    (h22376 : p469 ∨ p461 ∨ p457)
    (h22377 : p468 ∨ p461 ∨ p457)
    (h22378 : p467 ∨ p461 ∨ p457)
    (h22379 : (¬ p467) ∨ p457 ∨ p461 ∨ (¬ p468) ∨ (¬ p469) ∨ (¬ p465)) : p461 ∨ p457 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p461) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p457) := fun hu => hn (Or.inr hu)
  have u2 : p465 := by
    rcases h22375 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p469 := by
    rcases h22376 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p468 := by
    rcases h22377 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p467 := by
    rcases h22378 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22379 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u1 q1)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u2)

theorem step22382 (p41 p237 p382 p814 p819 p918 p1325 p1385 : Prop)
    (h20637 : (¬ p41) ∨ (¬ p237) ∨ (¬ p814) ∨ (¬ p918))
    (h17950 : (¬ p41) ∨ (¬ p382) ∨ (¬ p819) ∨ (¬ p1325) ∨ (¬ p1385))
    (h20985 : p819 ∨ p814) : (¬ p41) ∨ (¬ p1325) ∨ (¬ p1385) ∨ (¬ p918) ∨ (¬ p382) ∨ (¬ p237) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p814) := by
    rcases h20637 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u0)
    · exact False.elim (q1 u5)
    · exact q2
    · exact False.elim (q3 u3)
  have u7 : (¬ p819) := by
    rcases h17950 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u0)
    · exact False.elim (q1 u4)
    · exact q2
    · exact False.elim (q3 u1)
    · exact False.elim (q4 u2)
  rcases h20985 with q0 | q1
  · exact False.elim (u7 q0)
  · exact False.elim (u6 q1)

theorem step22383 (p3 p165 p188 p193 p237 : Prop)
    (h21673 : p3 ∨ (¬ p188) ∨ p165 ∨ (¬ p237) ∨ p193)
    (h11977 : (¬ p165) ∨ p193 ∨ (¬ p237)) : (¬ p188) ∨ p193 ∨ p3 ∨ (¬ p237) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p193) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p165 := by
    rcases h21673 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (u2 q0)
    · exact False.elim (q1 u0)
    · exact q2
    · exact False.elim (q3 u3)
    · exact False.elim (u1 q4)
  rcases h11977 with q0 | q1 | q2
  · exact False.elim (q0 u4)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)

theorem step22384 (p3 p188 p192 p193 p237 : Prop)
    (h21387 : p188 ∨ p192)
    (h22057 : p192 ∨ (¬ p193))
    (h22383 : (¬ p188) ∨ p193 ∨ p3 ∨ (¬ p237)) : p192 ∨ (¬ p237) ∨ p3 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p192) := fun hu => hn (Or.inl hu)
  have u1 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p3) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p188 := by
    rcases h21387 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : (¬ p193) := by
    rcases h22057 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h22383 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (u4 q1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u1)

theorem step22386 (p10 p101 p125 p304 p323 p329 p350 p384 p419 p434 p438 p1206 p1328 p1334 p1366 : Prop)
    (h21681 : p323 ∨ p10)
    (h21610 : p329 ∨ p10)
    (h12635 : (¬ p419) ∨ (¬ p1328) ∨ (¬ p1366))
    (h21955 : p125 ∨ (¬ p438) ∨ (¬ p1366) ∨ (¬ p304) ∨ (¬ p350) ∨ (¬ p101) ∨ (¬ p329))
    (h21365 : p1334 ∨ p1328)
    (h21060 : p438 ∨ p434)
    (h17008 : (¬ p323) ∨ (¬ p384) ∨ (¬ p434) ∨ (¬ p1206) ∨ (¬ p1334)) : (¬ p1366) ∨ (¬ p1206) ∨ (¬ p419) ∨ (¬ p101) ∨ (¬ p384) ∨ (¬ p350) ∨ p125 ∨ (¬ p304) ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p384 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p323 := by
    rcases h21681 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u10 : p329 := by
    rcases h21610 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u11 : (¬ p1328) := by
    rcases h12635 with q0 | q1 | q2
    · exact False.elim (q0 u2)
    · exact q1
    · exact False.elim (q2 u0)
  have u12 : (¬ p438) := by
    rcases h21955 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u6 q0)
    · exact q1
    · exact False.elim (q2 u0)
    · exact False.elim (q3 u7)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u3)
    · exact False.elim (q6 u10)
  have u13 : p1334 := by
    rcases h21365 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  have u14 : p434 := by
    rcases h21060 with q0 | q1
    · exact False.elim (u12 q0)
    · exact q1
  rcases h17008 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u14)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u13)

theorem step22391 (p84 p90 p92 p96 p97 p98 p99 p100 : Prop)
    (h499 : p92 ∨ p96)
    (h500 : p92 ∨ p97)
    (h501 : p92 ∨ p98)
    (h502 : p92 ∨ p99)
    (h503 : p92 ∨ p100)
    (h428 : p84 ∨ p90 ∨ (¬ p96) ∨ (¬ p97) ∨ (¬ p98) ∨ (¬ p99) ∨ (¬ p100)) : p92 ∨ p90 ∨ p84 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p92) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p90) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p84) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p96 := by
    rcases h499 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p97 := by
    rcases h500 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p98 := by
    rcases h501 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p99 := by
    rcases h502 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p100 := by
    rcases h503 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h428 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22392 (p84 p90 p91 p96 p97 p98 p99 p100 : Prop)
    (h494 : p91 ∨ p96)
    (h495 : p91 ∨ p97)
    (h496 : p91 ∨ p98)
    (h497 : p91 ∨ p99)
    (h498 : p91 ∨ p100)
    (h428 : p84 ∨ p90 ∨ (¬ p96) ∨ (¬ p97) ∨ (¬ p98) ∨ (¬ p99) ∨ (¬ p100)) : p91 ∨ p90 ∨ p84 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p91) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p90) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p84) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p96 := by
    rcases h494 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p97 := by
    rcases h495 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p98 := by
    rcases h496 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p99 := by
    rcases h497 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p100 := by
    rcases h498 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h428 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22393 (p84 p90 p95 p96 p97 p98 p99 p100 : Prop)
    (h514 : p95 ∨ p96)
    (h515 : p95 ∨ p97)
    (h516 : p95 ∨ p98)
    (h517 : p95 ∨ p99)
    (h518 : p95 ∨ p100)
    (h428 : p84 ∨ p90 ∨ (¬ p96) ∨ (¬ p97) ∨ (¬ p98) ∨ (¬ p99) ∨ (¬ p100)) : p95 ∨ p90 ∨ p84 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p95) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p90) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p84) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p96 := by
    rcases h514 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p97 := by
    rcases h515 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p98 := by
    rcases h516 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p99 := by
    rcases h517 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p100 := by
    rcases h518 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h428 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22394 (p84 p90 p94 p96 p97 p98 p99 p100 : Prop)
    (h509 : p94 ∨ p96)
    (h510 : p94 ∨ p97)
    (h511 : p94 ∨ p98)
    (h512 : p94 ∨ p99)
    (h513 : p94 ∨ p100)
    (h428 : p84 ∨ p90 ∨ (¬ p96) ∨ (¬ p97) ∨ (¬ p98) ∨ (¬ p99) ∨ (¬ p100)) : p94 ∨ p90 ∨ p84 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p94) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p90) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p84) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p96 := by
    rcases h509 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p97 := by
    rcases h510 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p98 := by
    rcases h511 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p99 := by
    rcases h512 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p100 := by
    rcases h513 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h428 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22395 (p84 p90 p91 p92 p93 p94 p95 p96 p97 p98 p99 p100 : Prop)
    (h403 : p84 ∨ p90 ∨ (¬ p91) ∨ (¬ p92) ∨ (¬ p93) ∨ (¬ p94) ∨ (¬ p95))
    (h504 : p93 ∨ p96)
    (h505 : p93 ∨ p97)
    (h506 : p93 ∨ p98)
    (h507 : p93 ∨ p99)
    (h508 : p93 ∨ p100)
    (h428 : p84 ∨ p90 ∨ (¬ p96) ∨ (¬ p97) ∨ (¬ p98) ∨ (¬ p99) ∨ (¬ p100)) : (¬ p94) ∨ (¬ p92) ∨ p84 ∨ p90 ∨ (¬ p95) ∨ (¬ p91) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p94 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p92 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p84) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p90) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p95 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p91 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p93) := by
    rcases h403 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u1)
    · exact q4
    · exact False.elim (q5 u0)
    · exact False.elim (q6 u4)
  have u7 : p96 := by
    rcases h504 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p97 := by
    rcases h505 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p98 := by
    rcases h506 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p99 := by
    rcases h507 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p100 := by
    rcases h508 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h428 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22396 (p84 p90 p91 p92 p94 p95 : Prop)
    (h22391 : p92 ∨ p90 ∨ p84)
    (h22392 : p91 ∨ p90 ∨ p84)
    (h22393 : p95 ∨ p90 ∨ p84)
    (h22394 : p94 ∨ p90 ∨ p84)
    (h22395 : (¬ p94) ∨ (¬ p92) ∨ p84 ∨ p90 ∨ (¬ p95) ∨ (¬ p91)) : p90 ∨ p84 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p90) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p84) := fun hu => hn (Or.inr hu)
  have u2 : p92 := by
    rcases h22391 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p91 := by
    rcases h22392 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p95 := by
    rcases h22393 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p94 := by
    rcases h22394 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22395 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22399 (p17 p84 p85 p89 p265 p266 p425 p495 p498 p574 p580 : Prop)
    (h21425 : p266 ∨ p17)
    (h21151 : p17 ∨ p265)
    (h22277 : p89 ∨ p84)
    (h22278 : p84 ∨ (¬ p85))
    (h8741 : (¬ p89) ∨ (¬ p266) ∨ p498)
    (h13630 : p85 ∨ (¬ p495) ∨ (¬ p580))
    (h8739 : (¬ p425) ∨ (¬ p495) ∨ (¬ p498))
    (h20972 : p574 ∨ p580)
    (h3237 : (¬ p265) ∨ p425 ∨ (¬ p574)) : p84 ∨ (¬ p495) ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p84) := fun hu => hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p266 := by
    rcases h21425 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : p265 := by
    rcases h21151 with q0 | q1
    · exact False.elim (u2 q0)
    · exact q1
  have u5 : p89 := by
    rcases h22277 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : (¬ p85) := by
    rcases h22278 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p498 := by
    rcases h8741 with q0 | q1 | q2
    · exact False.elim (q0 u5)
    · exact False.elim (q1 u3)
    · exact q2
  have u8 : (¬ p580) := by
    rcases h13630 with q0 | q1 | q2
    · exact False.elim (u6 q0)
    · exact False.elim (q1 u1)
    · exact q2
  have u9 : (¬ p425) := by
    rcases h8739 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u1)
    · exact False.elim (q2 u7)
  have u10 : p574 := by
    rcases h20972 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h3237 with q0 | q1 | q2
  · exact False.elim (q0 u4)
  · exact False.elim (u9 q1)
  · exact False.elim (q2 u10)

theorem step22402 (p139 p142 p144 p145 p146 p147 p148 p149 p150 p151 p152 p153 : Prop)
    (h678 : p139 ∨ p142 ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p147) ∨ (¬ p148))
    (h756 : p144 ∨ p149)
    (h757 : p144 ∨ p150)
    (h758 : p144 ∨ p151)
    (h759 : p144 ∨ p152)
    (h760 : p144 ∨ p153)
    (h703 : p139 ∨ p142 ∨ (¬ p149) ∨ (¬ p150) ∨ (¬ p151) ∨ (¬ p152) ∨ (¬ p153)) : (¬ p147) ∨ (¬ p146) ∨ p142 ∨ (¬ p148) ∨ p139 ∨ (¬ p145) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p147 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p146 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p142) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p148 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p139) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p145 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p144) := by
    rcases h678 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u4 q0)
    · exact False.elim (u2 q1)
    · exact q2
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact False.elim (q6 u3)
  have u7 : p149 := by
    rcases h756 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p150 := by
    rcases h757 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p151 := by
    rcases h758 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p152 := by
    rcases h759 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p153 := by
    rcases h760 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h703 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22403 (p139 p142 p145 p146 p147 p148 : Prop)
    (h21812 : p148 ∨ p139 ∨ p142)
    (h21813 : p147 ∨ p139 ∨ p142)
    (h21814 : p146 ∨ p139 ∨ p142)
    (h21815 : p145 ∨ p139 ∨ p142)
    (h22402 : (¬ p147) ∨ (¬ p146) ∨ p142 ∨ (¬ p148) ∨ p139 ∨ (¬ p145)) : p139 ∨ p142 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p139) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p142) := fun hu => hn (Or.inr hu)
  have u2 : p148 := by
    rcases h21812 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p147 := by
    rcases h21813 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p146 := by
    rcases h21814 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p145 := by
    rcases h21815 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22402 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (u0 q4)
  · exact False.elim (q5 u5)

theorem step22404 (p139 p142 : Prop)
    (h16166 : p139 ∨ (¬ p142))
    (h22403 : p139 ∨ p142) : p139 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p139) := fun hu => hn hu
  have u1 : (¬ p142) := by
    rcases h16166 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h22403 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)

theorem step22405 (p12 p104 p108 p139 p265 p304 p1076 : Prop)
    (h22404 : p139)
    (h7021 : (¬ p12) ∨ (¬ p104) ∨ (¬ p1076))
    (h16628 : (¬ p12) ∨ (¬ p108) ∨ (¬ p139) ∨ (¬ p265) ∨ (¬ p304) ∨ (¬ p1076))
    (h22239 : p108 ∨ p104) : (¬ p1076) ∨ (¬ p304) ∨ (¬ p265) ∨ (¬ p12) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p139 := by
    exact h22404
  have u5 : (¬ p104) := by
    rcases h7021 with q0 | q1 | q2
    · exact False.elim (q0 u3)
    · exact q1
    · exact False.elim (q2 u0)
  have u6 : (¬ p108) := by
    rcases h16628 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u3)
    · exact q1
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u2)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
  rcases h22239 with q0 | q1
  · exact False.elim (u6 q0)
  · exact False.elim (u5 q1)

theorem step22408 (p224 p666 p672 p675 p676 p677 p678 p679 : Prop)
    (h3869 : p672 ∨ p675)
    (h3870 : p672 ∨ p676)
    (h3871 : p672 ∨ p677)
    (h3872 : p672 ∨ p678)
    (h3873 : p672 ∨ p679)
    (h3794 : p224 ∨ p666 ∨ (¬ p675) ∨ (¬ p676) ∨ (¬ p677) ∨ (¬ p678) ∨ (¬ p679)) : p672 ∨ p666 ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p672) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p666) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p675 := by
    rcases h3869 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p676 := by
    rcases h3870 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p677 := by
    rcases h3871 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p678 := by
    rcases h3872 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p679 := by
    rcases h3873 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3794 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22409 (p224 p666 p671 p675 p676 p677 p678 p679 : Prop)
    (h3864 : p671 ∨ p675)
    (h3865 : p671 ∨ p676)
    (h3866 : p671 ∨ p677)
    (h3867 : p671 ∨ p678)
    (h3868 : p671 ∨ p679)
    (h3794 : p224 ∨ p666 ∨ (¬ p675) ∨ (¬ p676) ∨ (¬ p677) ∨ (¬ p678) ∨ (¬ p679)) : p671 ∨ p666 ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p671) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p666) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p675 := by
    rcases h3864 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p676 := by
    rcases h3865 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p677 := by
    rcases h3866 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p678 := by
    rcases h3867 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p679 := by
    rcases h3868 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3794 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22410 (p224 p666 p670 p675 p676 p677 p678 p679 : Prop)
    (h3859 : p670 ∨ p675)
    (h3860 : p670 ∨ p676)
    (h3861 : p670 ∨ p677)
    (h3862 : p670 ∨ p678)
    (h3863 : p670 ∨ p679)
    (h3794 : p224 ∨ p666 ∨ (¬ p675) ∨ (¬ p676) ∨ (¬ p677) ∨ (¬ p678) ∨ (¬ p679)) : p670 ∨ p666 ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p670) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p666) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p675 := by
    rcases h3859 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p676 := by
    rcases h3860 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p677 := by
    rcases h3861 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p678 := by
    rcases h3862 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p679 := by
    rcases h3863 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3794 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22411 (p224 p666 p674 p675 p676 p677 p678 p679 : Prop)
    (h3879 : p674 ∨ p675)
    (h3880 : p674 ∨ p676)
    (h3881 : p674 ∨ p677)
    (h3882 : p674 ∨ p678)
    (h3883 : p674 ∨ p679)
    (h3794 : p224 ∨ p666 ∨ (¬ p675) ∨ (¬ p676) ∨ (¬ p677) ∨ (¬ p678) ∨ (¬ p679)) : p674 ∨ p666 ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p674) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p666) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p675 := by
    rcases h3879 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p676 := by
    rcases h3880 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p677 := by
    rcases h3881 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p678 := by
    rcases h3882 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p679 := by
    rcases h3883 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3794 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22412 (p224 p666 p670 p671 p672 p673 p674 p675 p676 p677 p678 p679 : Prop)
    (h3769 : p224 ∨ p666 ∨ (¬ p670) ∨ (¬ p671) ∨ (¬ p672) ∨ (¬ p673) ∨ (¬ p674))
    (h3874 : p673 ∨ p675)
    (h3875 : p673 ∨ p676)
    (h3876 : p673 ∨ p677)
    (h3877 : p673 ∨ p678)
    (h3878 : p673 ∨ p679)
    (h3794 : p224 ∨ p666 ∨ (¬ p675) ∨ (¬ p676) ∨ (¬ p677) ∨ (¬ p678) ∨ (¬ p679)) : (¬ p674) ∨ (¬ p670) ∨ (¬ p671) ∨ p224 ∨ (¬ p672) ∨ p666 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p674 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p670 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p671 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p672 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p666) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p673) := by
    rcases h3769 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u5 q1)
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u2)
    · exact False.elim (q4 u4)
    · exact q5
    · exact False.elim (q6 u0)
  have u7 : p675 := by
    rcases h3874 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p676 := by
    rcases h3875 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p677 := by
    rcases h3876 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p678 := by
    rcases h3877 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p679 := by
    rcases h3878 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h3794 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22413 (p224 p666 p670 p671 p672 p674 : Prop)
    (h22408 : p672 ∨ p666 ∨ p224)
    (h22409 : p671 ∨ p666 ∨ p224)
    (h22410 : p670 ∨ p666 ∨ p224)
    (h22411 : p674 ∨ p666 ∨ p224)
    (h22412 : (¬ p674) ∨ (¬ p670) ∨ (¬ p671) ∨ p224 ∨ (¬ p672) ∨ p666) : p666 ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p666) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr hu)
  have u2 : p672 := by
    rcases h22408 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p671 := by
    rcases h22409 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p670 := by
    rcases h22410 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p674 := by
    rcases h22411 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22412 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (u0 q5)

theorem step22414 (p63 p836 p897 p904 p923 p927 p928 p930 p931 p932 p933 p934 p935 p936 p937 p938 p939 p1096 p1116 : Prop)
    (h20784 : p897 ∨ p904)
    (h15922 : (¬ p836) ∨ p897 ∨ (¬ p923))
    (h20439 : (¬ p836) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1116))
    (h22015 : p934 ∨ p923 ∨ p928)
    (h22016 : p933 ∨ p923 ∨ p928)
    (h22017 : p932 ∨ p923 ∨ p928)
    (h22018 : p931 ∨ p923 ∨ p928)
    (h13901 : (¬ p63) ∨ (¬ p927) ∨ p1096)
    (h5340 : p923 ∨ p928 ∨ (¬ p930) ∨ (¬ p931) ∨ (¬ p932) ∨ (¬ p933) ∨ (¬ p934))
    (h5433 : p930 ∨ p935)
    (h5434 : p930 ∨ p936)
    (h5435 : p930 ∨ p937)
    (h5436 : p930 ∨ p938)
    (h5437 : p930 ∨ p939)
    (h5364 : p923 ∨ p927 ∨ (¬ p935) ∨ (¬ p936) ∨ (¬ p937) ∨ (¬ p938) ∨ (¬ p939)) : p897 ∨ p928 ∨ (¬ p836) ∨ (¬ p63) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p897) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p928) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p904 := by
    rcases h20784 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : (¬ p923) := by
    rcases h15922 with q0 | q1 | q2
    · exact False.elim (q0 u2)
    · exact False.elim (u0 q1)
    · exact q2
  have u7 : (¬ p1096) := by
    rcases h20439 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u2)
    · exact False.elim (q1 u5)
    · exact q2
    · exact False.elim (q3 u4)
  have u8 : p934 := by
    rcases h22015 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u6 q1)
    · exact False.elim (u1 q2)
  have u9 : p933 := by
    rcases h22016 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u6 q1)
    · exact False.elim (u1 q2)
  have u10 : p932 := by
    rcases h22017 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u6 q1)
    · exact False.elim (u1 q2)
  have u11 : p931 := by
    rcases h22018 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u6 q1)
    · exact False.elim (u1 q2)
  have u12 : (¬ p927) := by
    rcases h13901 with q0 | q1 | q2
    · exact False.elim (q0 u3)
    · exact q1
    · exact False.elim (u7 q2)
  have u13 : (¬ p930) := by
    rcases h5340 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u6 q0)
    · exact False.elim (u1 q1)
    · exact q2
    · exact False.elim (q3 u11)
    · exact False.elim (q4 u10)
    · exact False.elim (q5 u9)
    · exact False.elim (q6 u8)
  have u14 : p935 := by
    rcases h5433 with q0 | q1
    · exact False.elim (u13 q0)
    · exact q1
  have u15 : p936 := by
    rcases h5434 with q0 | q1
    · exact False.elim (u13 q0)
    · exact q1
  have u16 : p937 := by
    rcases h5435 with q0 | q1
    · exact False.elim (u13 q0)
    · exact q1
  have u17 : p938 := by
    rcases h5436 with q0 | q1
    · exact False.elim (u13 q0)
    · exact q1
  have u18 : p939 := by
    rcases h5437 with q0 | q1
    · exact False.elim (u13 q0)
    · exact q1
  rcases h5364 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (u12 q1)
  · exact False.elim (q2 u14)
  · exact False.elim (q3 u15)
  · exact False.elim (q4 u16)
  · exact False.elim (q5 u17)
  · exact False.elim (q6 u18)

theorem step22415 (p922 p928 p931 p935 p936 p937 p938 p939 : Prop)
    (h5438 : p931 ∨ p935)
    (h5439 : p931 ∨ p936)
    (h5440 : p931 ∨ p937)
    (h5441 : p931 ∨ p938)
    (h5442 : p931 ∨ p939)
    (h5360 : p922 ∨ p928 ∨ (¬ p935) ∨ (¬ p936) ∨ (¬ p937) ∨ (¬ p938) ∨ (¬ p939)) : p931 ∨ p922 ∨ p928 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p931) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p922) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p928) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p935 := by
    rcases h5438 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p936 := by
    rcases h5439 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p937 := by
    rcases h5440 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p938 := by
    rcases h5441 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p939 := by
    rcases h5442 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5360 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22416 (p922 p928 p930 p935 p936 p937 p938 p939 : Prop)
    (h5433 : p930 ∨ p935)
    (h5434 : p930 ∨ p936)
    (h5435 : p930 ∨ p937)
    (h5436 : p930 ∨ p938)
    (h5437 : p930 ∨ p939)
    (h5360 : p922 ∨ p928 ∨ (¬ p935) ∨ (¬ p936) ∨ (¬ p937) ∨ (¬ p938) ∨ (¬ p939)) : p930 ∨ p922 ∨ p928 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p930) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p922) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p928) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p935 := by
    rcases h5433 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p936 := by
    rcases h5434 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p937 := by
    rcases h5435 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p938 := by
    rcases h5436 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p939 := by
    rcases h5437 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5360 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22417 (p922 p928 p934 p935 p936 p937 p938 p939 : Prop)
    (h5453 : p934 ∨ p935)
    (h5454 : p934 ∨ p936)
    (h5455 : p934 ∨ p937)
    (h5456 : p934 ∨ p938)
    (h5457 : p934 ∨ p939)
    (h5360 : p922 ∨ p928 ∨ (¬ p935) ∨ (¬ p936) ∨ (¬ p937) ∨ (¬ p938) ∨ (¬ p939)) : p934 ∨ p922 ∨ p928 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p934) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p922) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p928) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p935 := by
    rcases h5453 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p936 := by
    rcases h5454 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p937 := by
    rcases h5455 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p938 := by
    rcases h5456 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p939 := by
    rcases h5457 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5360 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22418 (p922 p928 p933 p935 p936 p937 p938 p939 : Prop)
    (h5448 : p933 ∨ p935)
    (h5449 : p933 ∨ p936)
    (h5450 : p933 ∨ p937)
    (h5451 : p933 ∨ p938)
    (h5452 : p933 ∨ p939)
    (h5360 : p922 ∨ p928 ∨ (¬ p935) ∨ (¬ p936) ∨ (¬ p937) ∨ (¬ p938) ∨ (¬ p939)) : p933 ∨ p922 ∨ p928 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p933) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p922) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p928) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p935 := by
    rcases h5448 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p936 := by
    rcases h5449 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p937 := by
    rcases h5450 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p938 := by
    rcases h5451 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p939 := by
    rcases h5452 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5360 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22419 (p41 p89 p237 p922 p926 p928 p930 p931 p932 p933 p934 p935 p936 p937 p938 p939 p1074 p1116 : Prop)
    (h13519 : (¬ p926) ∨ (¬ p1074) ∨ (¬ p1116))
    (h17517 : (¬ p41) ∨ (¬ p89) ∨ (¬ p237) ∨ (¬ p922) ∨ (¬ p1074) ∨ (¬ p1116))
    (h22415 : p931 ∨ p922 ∨ p928)
    (h22416 : p930 ∨ p922 ∨ p928)
    (h22417 : p934 ∨ p922 ∨ p928)
    (h22418 : p933 ∨ p922 ∨ p928)
    (h5333 : p922 ∨ p926 ∨ (¬ p930) ∨ (¬ p931) ∨ (¬ p932) ∨ (¬ p933) ∨ (¬ p934))
    (h5443 : p932 ∨ p935)
    (h5444 : p932 ∨ p936)
    (h5445 : p932 ∨ p937)
    (h5446 : p932 ∨ p938)
    (h5447 : p932 ∨ p939)
    (h5360 : p922 ∨ p928 ∨ (¬ p935) ∨ (¬ p936) ∨ (¬ p937) ∨ (¬ p938) ∨ (¬ p939)) : (¬ p1074) ∨ p928 ∨ (¬ p41) ∨ (¬ p89) ∨ (¬ p1116) ∨ (¬ p237) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p928) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p926) := by
    rcases h13519 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u4)
  have u7 : (¬ p922) := by
    rcases h17517 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u2)
    · exact False.elim (q1 u3)
    · exact False.elim (q2 u5)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u4)
  have u8 : p931 := by
    rcases h22415 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u7 q1)
    · exact False.elim (u1 q2)
  have u9 : p930 := by
    rcases h22416 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u7 q1)
    · exact False.elim (u1 q2)
  have u10 : p934 := by
    rcases h22417 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u7 q1)
    · exact False.elim (u1 q2)
  have u11 : p933 := by
    rcases h22418 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u7 q1)
    · exact False.elim (u1 q2)
  have u12 : (¬ p932) := by
    rcases h5333 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u7 q0)
    · exact False.elim (u6 q1)
    · exact False.elim (q2 u9)
    · exact False.elim (q3 u8)
    · exact q4
    · exact False.elim (q5 u11)
    · exact False.elim (q6 u10)
  have u13 : p935 := by
    rcases h5443 with q0 | q1
    · exact False.elim (u12 q0)
    · exact q1
  have u14 : p936 := by
    rcases h5444 with q0 | q1
    · exact False.elim (u12 q0)
    · exact q1
  have u15 : p937 := by
    rcases h5445 with q0 | q1
    · exact False.elim (u12 q0)
    · exact q1
  have u16 : p938 := by
    rcases h5446 with q0 | q1
    · exact False.elim (u12 q0)
    · exact q1
  have u17 : p939 := by
    rcases h5447 with q0 | q1
    · exact False.elim (u12 q0)
    · exact q1
  rcases h5360 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u7 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u13)
  · exact False.elim (q3 u14)
  · exact False.elim (q4 u15)
  · exact False.elim (q5 u16)
  · exact False.elim (q6 u17)

theorem step22420 (p224 p431 p666 p734 p836 p1116 p1332 : Prop)
    (h22413 : p666 ∨ p224)
    (h10844 : p224 ∨ (¬ p734) ∨ (¬ p1332))
    (h17352 : (¬ p431) ∨ (¬ p666) ∨ (¬ p734) ∨ (¬ p836) ∨ (¬ p1116))
    (h22367 : p431 ∨ p1332) : (¬ p734) ∨ p224 ∨ (¬ p836) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p666 := by
    rcases h22413 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : (¬ p1332) := by
    rcases h10844 with q0 | q1 | q2
    · exact False.elim (u1 q0)
    · exact False.elim (q1 u0)
    · exact q2
  have u6 : (¬ p431) := by
    rcases h17352 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u4)
    · exact False.elim (q2 u0)
    · exact False.elim (q3 u2)
    · exact False.elim (q4 u3)
  rcases h22367 with q0 | q1
  · exact False.elim (u6 q0)
  · exact False.elim (u5 q1)

theorem step22421 (p1387 p1393 p1400 p1401 p1402 p1403 p1404 p1405 : Prop)
    (h8469 : p1400 ∨ p1401)
    (h8470 : p1400 ∨ p1402)
    (h8471 : p1400 ∨ p1403)
    (h8472 : p1400 ∨ p1404)
    (h8473 : p1400 ∨ p1405)
    (h8376 : p1387 ∨ p1393 ∨ (¬ p1401) ∨ (¬ p1402) ∨ (¬ p1403) ∨ (¬ p1404) ∨ (¬ p1405)) : p1400 ∨ p1387 ∨ p1393 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1400) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1387) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1393) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1401 := by
    rcases h8469 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1402 := by
    rcases h8470 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1403 := by
    rcases h8471 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1404 := by
    rcases h8472 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1405 := by
    rcases h8473 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8376 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22422 (p1387 p1393 p1396 p1401 p1402 p1403 p1404 p1405 : Prop)
    (h8449 : p1396 ∨ p1401)
    (h8450 : p1396 ∨ p1402)
    (h8451 : p1396 ∨ p1403)
    (h8452 : p1396 ∨ p1404)
    (h8453 : p1396 ∨ p1405)
    (h8376 : p1387 ∨ p1393 ∨ (¬ p1401) ∨ (¬ p1402) ∨ (¬ p1403) ∨ (¬ p1404) ∨ (¬ p1405)) : p1396 ∨ p1387 ∨ p1393 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1396) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1387) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1393) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1401 := by
    rcases h8449 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1402 := by
    rcases h8450 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1403 := by
    rcases h8451 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1404 := by
    rcases h8452 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1405 := by
    rcases h8453 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8376 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22423 (p1387 p1393 p1399 p1401 p1402 p1403 p1404 p1405 : Prop)
    (h8464 : p1399 ∨ p1401)
    (h8465 : p1399 ∨ p1402)
    (h8466 : p1399 ∨ p1403)
    (h8467 : p1399 ∨ p1404)
    (h8468 : p1399 ∨ p1405)
    (h8376 : p1387 ∨ p1393 ∨ (¬ p1401) ∨ (¬ p1402) ∨ (¬ p1403) ∨ (¬ p1404) ∨ (¬ p1405)) : p1399 ∨ p1387 ∨ p1393 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1399) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1387) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1393) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1401 := by
    rcases h8464 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1402 := by
    rcases h8465 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1403 := by
    rcases h8466 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1404 := by
    rcases h8467 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1405 := by
    rcases h8468 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8376 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22424 (p1387 p1393 p1398 p1401 p1402 p1403 p1404 p1405 : Prop)
    (h8459 : p1398 ∨ p1401)
    (h8460 : p1398 ∨ p1402)
    (h8461 : p1398 ∨ p1403)
    (h8462 : p1398 ∨ p1404)
    (h8463 : p1398 ∨ p1405)
    (h8376 : p1387 ∨ p1393 ∨ (¬ p1401) ∨ (¬ p1402) ∨ (¬ p1403) ∨ (¬ p1404) ∨ (¬ p1405)) : p1398 ∨ p1387 ∨ p1393 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1398) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1387) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1393) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1401 := by
    rcases h8459 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1402 := by
    rcases h8460 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1403 := by
    rcases h8461 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1404 := by
    rcases h8462 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1405 := by
    rcases h8463 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8376 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22425 (p1387 p1393 p1396 p1397 p1398 p1399 p1400 p1401 p1402 p1403 p1404 p1405 : Prop)
    (h8351 : p1387 ∨ p1393 ∨ (¬ p1396) ∨ (¬ p1397) ∨ (¬ p1398) ∨ (¬ p1399) ∨ (¬ p1400))
    (h8454 : p1397 ∨ p1401)
    (h8455 : p1397 ∨ p1402)
    (h8456 : p1397 ∨ p1403)
    (h8457 : p1397 ∨ p1404)
    (h8458 : p1397 ∨ p1405)
    (h8376 : p1387 ∨ p1393 ∨ (¬ p1401) ∨ (¬ p1402) ∨ (¬ p1403) ∨ (¬ p1404) ∨ (¬ p1405)) : (¬ p1398) ∨ (¬ p1400) ∨ p1393 ∨ p1387 ∨ (¬ p1399) ∨ (¬ p1396) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1398 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1400 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1393) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1387) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1399 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1396 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1397) := by
    rcases h8351 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u5)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u1)
  have u7 : p1401 := by
    rcases h8454 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1402 := by
    rcases h8455 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1403 := by
    rcases h8456 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1404 := by
    rcases h8457 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1405 := by
    rcases h8458 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h8376 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22426 (p1387 p1393 p1396 p1398 p1399 p1400 : Prop)
    (h22421 : p1400 ∨ p1387 ∨ p1393)
    (h22422 : p1396 ∨ p1387 ∨ p1393)
    (h22423 : p1399 ∨ p1387 ∨ p1393)
    (h22424 : p1398 ∨ p1387 ∨ p1393)
    (h22425 : (¬ p1398) ∨ (¬ p1400) ∨ p1393 ∨ p1387 ∨ (¬ p1399) ∨ (¬ p1396)) : p1387 ∨ p1393 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1387) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1393) := fun hu => hn (Or.inr hu)
  have u2 : p1400 := by
    rcases h22421 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1396 := by
    rcases h22422 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1399 := by
    rcases h22423 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1398 := by
    rcases h22424 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22425 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22427 (p2 p67 p419 p1189 p1193 p1286 p1287 : Prop)
    (h20657 : p1287 ∨ p1286)
    (h13501 : (¬ p419) ∨ (¬ p1189) ∨ p1287)
    (h17189 : (¬ p2) ∨ (¬ p67) ∨ (¬ p419) ∨ (¬ p1193) ∨ (¬ p1286))
    (h21784 : p1189 ∨ p1193) : p1287 ∨ (¬ p419) ∨ (¬ p2) ∨ (¬ p67) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1287) := fun hu => hn (Or.inl hu)
  have u1 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1286 := by
    rcases h20657 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : (¬ p1189) := by
    rcases h13501 with q0 | q1 | q2
    · exact False.elim (q0 u1)
    · exact q1
    · exact False.elim (u0 q2)
  have u6 : (¬ p1193) := by
    rcases h17189 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u2)
    · exact False.elim (q1 u3)
    · exact False.elim (q2 u1)
    · exact q3
    · exact False.elim (q4 u4)
  rcases h21784 with q0 | q1
  · exact False.elim (u5 q0)
  · exact False.elim (u6 q1)

theorem step22429 (p327 p328 p332 p337 p338 p339 p340 p341 : Prop)
    (h1799 : p332 ∨ p337)
    (h1800 : p332 ∨ p338)
    (h1801 : p332 ∨ p339)
    (h1802 : p332 ∨ p340)
    (h1803 : p332 ∨ p341)
    (h1744 : p327 ∨ p328 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341)) : p332 ∨ p327 ∨ p328 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p332) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p327) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p328) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p337 := by
    rcases h1799 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p338 := by
    rcases h1800 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p339 := by
    rcases h1801 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p340 := by
    rcases h1802 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p341 := by
    rcases h1803 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1744 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22430 (p327 p328 p336 p337 p338 p339 p340 p341 : Prop)
    (h1819 : p336 ∨ p337)
    (h1820 : p336 ∨ p338)
    (h1821 : p336 ∨ p339)
    (h1822 : p336 ∨ p340)
    (h1823 : p336 ∨ p341)
    (h1744 : p327 ∨ p328 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341)) : p336 ∨ p327 ∨ p328 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p336) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p327) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p328) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p337 := by
    rcases h1819 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p338 := by
    rcases h1820 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p339 := by
    rcases h1821 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p340 := by
    rcases h1822 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p341 := by
    rcases h1823 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1744 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22431 (p327 p328 p335 p337 p338 p339 p340 p341 : Prop)
    (h1814 : p335 ∨ p337)
    (h1815 : p335 ∨ p338)
    (h1816 : p335 ∨ p339)
    (h1817 : p335 ∨ p340)
    (h1818 : p335 ∨ p341)
    (h1744 : p327 ∨ p328 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341)) : p335 ∨ p327 ∨ p328 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p335) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p327) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p328) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p337 := by
    rcases h1814 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p338 := by
    rcases h1815 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p339 := by
    rcases h1816 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p340 := by
    rcases h1817 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p341 := by
    rcases h1818 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1744 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22432 (p327 p328 p334 p337 p338 p339 p340 p341 : Prop)
    (h1809 : p334 ∨ p337)
    (h1810 : p334 ∨ p338)
    (h1811 : p334 ∨ p339)
    (h1812 : p334 ∨ p340)
    (h1813 : p334 ∨ p341)
    (h1744 : p327 ∨ p328 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341)) : p334 ∨ p327 ∨ p328 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p334) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p327) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p328) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p337 := by
    rcases h1809 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p338 := by
    rcases h1810 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p339 := by
    rcases h1811 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p340 := by
    rcases h1812 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p341 := by
    rcases h1813 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1744 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22434 (p2 p5 p63 p419 p665 p666 p928 p983 p1116 p1325 p1333 : Prop)
    (h17977 : (¬ p2) ∨ (¬ p5) ∨ (¬ p63) ∨ (¬ p419) ∨ (¬ p665) ∨ (¬ p928) ∨ (¬ p1116))
    (h18598 : (¬ p63) ∨ (¬ p928) ∨ (¬ p983) ∨ (¬ p1116))
    (h16960 : p665 ∨ (¬ p1325))
    (h15453 : (¬ p666) ∨ p983 ∨ (¬ p1333))
    (h21656 : p1325 ∨ p1333) : (¬ p928) ∨ (¬ p666) ∨ (¬ p63) ∨ (¬ p419) ∨ (¬ p5) ∨ (¬ p1116) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p666 := by
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
  have u4 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p665) := by
    rcases h17977 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u6)
    · exact False.elim (q1 u4)
    · exact False.elim (q2 u2)
    · exact False.elim (q3 u3)
    · exact q4
    · exact False.elim (q5 u0)
    · exact False.elim (q6 u5)
  have u8 : (¬ p983) := by
    rcases h18598 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u2)
    · exact False.elim (q1 u0)
    · exact q2
    · exact False.elim (q3 u5)
  have u9 : (¬ p1325) := by
    rcases h16960 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : (¬ p1333) := by
    rcases h15453 with q0 | q1 | q2
    · exact False.elim (q0 u1)
    · exact False.elim (u8 q1)
    · exact q2
  rcases h21656 with q0 | q1
  · exact False.elim (u9 q0)
  · exact False.elim (u10 q1)

theorem step22438 (p835 p839 p844 p848 p849 p850 p851 p852 : Prop)
    (h4900 : p844 ∨ p848)
    (h4901 : p844 ∨ p849)
    (h4902 : p844 ∨ p850)
    (h4903 : p844 ∨ p851)
    (h4904 : p844 ∨ p852)
    (h4826 : p835 ∨ p839 ∨ (¬ p848) ∨ (¬ p849) ∨ (¬ p850) ∨ (¬ p851) ∨ (¬ p852)) : p844 ∨ p839 ∨ p835 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p844) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p839) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p835) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p848 := by
    rcases h4900 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p849 := by
    rcases h4901 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p850 := by
    rcases h4902 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p851 := by
    rcases h4903 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p852 := by
    rcases h4904 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4826 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22439 (p835 p839 p843 p848 p849 p850 p851 p852 : Prop)
    (h4895 : p843 ∨ p848)
    (h4896 : p843 ∨ p849)
    (h4897 : p843 ∨ p850)
    (h4898 : p843 ∨ p851)
    (h4899 : p843 ∨ p852)
    (h4826 : p835 ∨ p839 ∨ (¬ p848) ∨ (¬ p849) ∨ (¬ p850) ∨ (¬ p851) ∨ (¬ p852)) : p843 ∨ p839 ∨ p835 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p843) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p839) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p835) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p848 := by
    rcases h4895 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p849 := by
    rcases h4896 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p850 := by
    rcases h4897 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p851 := by
    rcases h4898 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p852 := by
    rcases h4899 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4826 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22440 (p835 p839 p847 p848 p849 p850 p851 p852 : Prop)
    (h4915 : p847 ∨ p848)
    (h4916 : p847 ∨ p849)
    (h4917 : p847 ∨ p850)
    (h4918 : p847 ∨ p851)
    (h4919 : p847 ∨ p852)
    (h4826 : p835 ∨ p839 ∨ (¬ p848) ∨ (¬ p849) ∨ (¬ p850) ∨ (¬ p851) ∨ (¬ p852)) : p847 ∨ p839 ∨ p835 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p847) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p839) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p835) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p848 := by
    rcases h4915 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p849 := by
    rcases h4916 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p850 := by
    rcases h4917 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p851 := by
    rcases h4918 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p852 := by
    rcases h4919 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4826 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22441 (p835 p839 p846 p848 p849 p850 p851 p852 : Prop)
    (h4910 : p846 ∨ p848)
    (h4911 : p846 ∨ p849)
    (h4912 : p846 ∨ p850)
    (h4913 : p846 ∨ p851)
    (h4914 : p846 ∨ p852)
    (h4826 : p835 ∨ p839 ∨ (¬ p848) ∨ (¬ p849) ∨ (¬ p850) ∨ (¬ p851) ∨ (¬ p852)) : p846 ∨ p839 ∨ p835 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p846) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p839) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p835) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p848 := by
    rcases h4910 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p849 := by
    rcases h4911 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p850 := by
    rcases h4912 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p851 := by
    rcases h4913 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p852 := by
    rcases h4914 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4826 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22442 (p835 p836 p839 p843 p844 p845 p846 p847 p848 p849 p850 p851 p852 : Prop)
    (h22438 : p844 ∨ p839 ∨ p835)
    (h22439 : p843 ∨ p839 ∨ p835)
    (h22440 : p847 ∨ p839 ∨ p835)
    (h22441 : p846 ∨ p839 ∨ p835)
    (h4806 : p836 ∨ p839 ∨ (¬ p843) ∨ (¬ p844) ∨ (¬ p845) ∨ (¬ p846) ∨ (¬ p847))
    (h4905 : p845 ∨ p848)
    (h4906 : p845 ∨ p849)
    (h4907 : p845 ∨ p850)
    (h4908 : p845 ∨ p851)
    (h4909 : p845 ∨ p852)
    (h4826 : p835 ∨ p839 ∨ (¬ p848) ∨ (¬ p849) ∨ (¬ p850) ∨ (¬ p851) ∨ (¬ p852)) : p839 ∨ p835 ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p839) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p835) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p844 := by
    rcases h22438 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p843 := by
    rcases h22439 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p847 := by
    rcases h22440 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p846 := by
    rcases h22441 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p845) := by
    rcases h4806 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u3)
    · exact q4
    · exact False.elim (q5 u6)
    · exact False.elim (q6 u5)
  have u8 : p848 := by
    rcases h4905 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p849 := by
    rcases h4906 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p850 := by
    rcases h4907 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p851 := by
    rcases h4908 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u12 : p852 := by
    rcases h4909 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h4826 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u12)

#print axioms step22442

end NineRUPTrial
